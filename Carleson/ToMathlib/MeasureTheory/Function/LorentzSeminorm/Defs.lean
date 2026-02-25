import Carleson.ToMathlib.MeasureTheory.Measure.AEMeasurable
import Carleson.ToMathlib.Rearrangement

-- Upstreaming status: NOT READY yet (mostly); this file is being actively worked on.
-- Needs significant clean-up (refactoring, code style, extracting lemmas etc.) first.


/-!
# Lorentz space

This file describes properties of almost everywhere strongly measurable functions with finite
`(p,q)`-seminorm, denoted by `eLorentzNorm f p q μ`.

The Prop-valued `MemLorentz f p q μ` states that a function `f : α → ε` has finite `(p,q)`-seminorm
and is almost everywhere strongly measurable.

## Main definitions
* TODO

-/

noncomputable section

open scoped NNReal ENNReal

variable {α ε ε' : Type*} {m m0 : MeasurableSpace α} {p q : ℝ≥0∞} [ENorm ε] [ENorm ε']

namespace MeasureTheory

section Lorentz

/-- The Lorentz seminorm of a function, for `0 < p < ∞` -/
def eLorentzNorm' (f : α → ε) (p : ℝ≥0∞) (q : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  p ^ q⁻¹.toReal * eLpNorm (fun (t : ℝ≥0) ↦ t * distribution f t μ ^ p⁻¹.toReal) q
    (volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹))

@[simp]
lemma eLorentzNorm'_exponent_zero' {f : α → ε} {μ : Measure α} : eLorentzNorm' f p 0 μ = 0 := by
  simp [eLorentzNorm']

private lemma ae_withDensity_inv_eq :
    ae ((volume : Measure ℝ≥0).withDensity (fun t ↦ (↑t : ℝ≥0∞)⁻¹)) =
    ae (volume : Measure ℝ≥0) := by
  ext s
  change (∀ᵐ x ∂(volume : Measure ℝ≥0).withDensity _, x ∈ s) ↔
    (∀ᵐ x ∂(volume : Measure ℝ≥0), x ∈ s)
  rw [ae_withDensity_iff (by measurability : Measurable (fun (t : ℝ≥0) ↦ (↑t : ℝ≥0∞)⁻¹))]
  exact ⟨fun h => h.mono fun x hx => hx (by simp), fun h => h.mono fun x hx _ => hx⟩

lemma eLorentzNorm'_eq (p_nonzero : p ≠ 0) (p_ne_top : p ≠ ⊤) {f : α → ε} {μ : Measure α} :
  eLorentzNorm' f p q μ
    = eLpNorm (fun (t : ℝ≥0) ↦ t ^ p⁻¹.toReal * rearrangement f t μ) q
        (volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹)) := by
  sorry


lemma eLorentzNorm'_eq' (p_nonzero : p ≠ 0) (p_ne_top : p ≠ ⊤) {f : α → ε} {μ : Measure α} :
  eLorentzNorm' f p q μ
    = eLpNorm (fun (t : ℝ≥0) ↦ t ^ (p⁻¹.toReal - q⁻¹.toReal) * rearrangement f t μ) q := by
  rcases eq_or_ne q 0 with rfl | q_nonzero
  · simp [eLorentzNorm'_exponent_zero', eLpNorm_exponent_zero]
  rcases eq_or_ne q ⊤ with rfl | q_ne_top
  · simp only [ENNReal.inv_top, ENNReal.toReal_zero, sub_zero]
    rw [eLorentzNorm'_eq p_nonzero p_ne_top, eLpNorm_exponent_top, eLpNorm_exponent_top]
    simp only [eLpNormEssSup, essSup, enorm_eq_self, ae_withDensity_inv_eq]
  · rw [eLorentzNorm'_eq p_nonzero p_ne_top,
        eLpNorm_eq_lintegral_rpow_enorm_toReal q_nonzero q_ne_top,
        eLpNorm_eq_lintegral_rpow_enorm_toReal q_nonzero q_ne_top]
    simp only [enorm_eq_self]
    congr 1
    rw [lintegral_withDensity_eq_lintegral_mul₀' (by measurability)]
    · apply lintegral_congr_ae
      have hae : ∀ᵐ (t : ℝ≥0) ∂(volume : Measure ℝ≥0), (t : ℝ≥0∞) ≠ 0 := by
        rw [ae_iff]
        have : {a : ℝ≥0 | ¬(a : ℝ≥0∞) ≠ 0} = {0} := by ext x; simp [ENNReal.coe_eq_zero]
        rw [this]; exact measure_singleton 0
      filter_upwards [hae] with t ht
      simp only [Pi.mul_apply]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0:ℝ) ≤ q.toReal),
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0:ℝ) ≤ q.toReal),
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          show (↑t : ℝ≥0∞)⁻¹ = (↑t : ℝ≥0∞) ^ (-1 : ℝ) from by simp [ENNReal.rpow_neg_one],
          ← mul_assoc, ← ENNReal.rpow_add _ _ ht ENNReal.coe_ne_top]
      congr 2
      rw [ENNReal.toReal_inv q]
      have hq : q.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨q_nonzero, q_ne_top⟩
      field_simp; linarith
    · measurability

lemma eLorentzNorm'_eq_integral_distribution_rpow {_ : MeasurableSpace α} {f : α → ε}
  {μ : Measure α} :
    eLorentzNorm' f p 1 μ = p * ∫⁻ (t : ℝ≥0), distribution f t μ ^ p.toReal⁻¹ := by
  unfold eLorentzNorm'
  simp only [inv_one, ENNReal.toReal_one, ENNReal.rpow_one, ENNReal.toReal_inv]
  congr
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  rw [lintegral_withDensity_eq_lintegral_mul₀' (by measurability)
    (by apply aeMeasurable_withDensity_inv; apply AEMeasurable.pow_const; apply AEStronglyMeasurable.enorm; apply
      aestronglyMeasurable_iff_aemeasurable.mpr; apply Measurable.aemeasurable; measurability)]
  simp only [enorm_eq_self, ENNReal.toReal_one, ENNReal.rpow_one, Pi.mul_apply, ne_eq, one_ne_zero,
    not_false_eq_true, div_self]
  rw [lintegral_nnreal_eq_lintegral_toNNReal_Ioi, lintegral_nnreal_eq_lintegral_toNNReal_Ioi]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only
  rw [← mul_assoc, ENNReal.inv_mul_cancel, one_mul]
  · rw [ENNReal.coe_ne_zero]
    symm
    apply ne_of_lt
    rw [Real.toNNReal_pos]
    exact hx
  · exact ENNReal.coe_ne_top

/-- The Lorentz seminorm of a function -/
def eLorentzNorm (f : α → ε) (p q : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  if p = 0 then 0 else if p = ∞ then
    (if q = 0 then 0 else if q = ∞ then eLpNormEssSup f μ else ∞ * eLpNormEssSup f μ)
  else eLorentzNorm' f p q μ

variable {μ : Measure α}

lemma eLorentzNorm_eq_eLorentzNorm' (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) {f : α → ε} :
    eLorentzNorm f p q μ = eLorentzNorm' f p q μ := by
  unfold eLorentzNorm
  simp [hp_ne_zero, hp_ne_top]

--TODO: remove this?
lemma eLorentzNorm_eq (p_nonzero : p ≠ 0) (p_ne_top : p ≠ ⊤) {f : α → ε} :
  eLorentzNorm f p q μ
    = eLpNorm (fun (t : ℝ≥0) ↦ t ^ p⁻¹.toReal * rearrangement f t μ) q
        (volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹)) := by
  unfold eLorentzNorm
  split_ifs with hp0
  · contradiction
  exact eLorentzNorm'_eq p_nonzero p_ne_top


@[simp]
lemma eLorentzNorm_exponent_zero {f : α → ε} : eLorentzNorm f 0 q μ = 0 := by simp [eLorentzNorm]

@[simp]
lemma eLorentzNorm_exponent_zero' {f : α → ε} : eLorentzNorm f p 0 μ = 0 := by
  simp [eLorentzNorm, eLorentzNorm']

@[simp]
lemma eLorentzNorm_exponent_top_top {f : α → ε} : eLorentzNorm f ∞ ∞ μ = eLpNormEssSup f μ := by
  simp [eLorentzNorm]

lemma eLorentzNorm_exponent_top' {f : α → ε} (q_ne_zero : q ≠ 0) (q_ne_top : q ≠ ⊤) (hf : eLpNormEssSup f μ ≠ 0) :
    eLorentzNorm f ∞ q μ = ∞ := by
  simp only [eLorentzNorm, ENNReal.top_ne_zero, ↓reduceIte]
  rw [ite_cond_eq_false, ite_cond_eq_false, ENNReal.top_mul hf] <;> simpa

lemma eLorentzNorm_exponent_top {ε} [TopologicalSpace ε] [ENormedAddMonoid ε] {f : α → ε}
  (q_ne_zero : q ≠ 0) (q_ne_top : q ≠ ⊤) (hf : ¬ f =ᶠ[ae μ] 0) :
    eLorentzNorm f ∞ q μ = ∞ := by
  apply eLorentzNorm_exponent_top' q_ne_zero q_ne_top
  contrapose! hf
  exact eLpNormEssSup_eq_zero_iff.mp hf

/-- A function is in the Lorentz space `L^{p,q}` if it is (strongly a.e.)-measurable and
  has finite Lorentz seminorm. -/
def MemLorentz [TopologicalSpace ε] (f : α → ε) (p r : ℝ≥0∞) (μ : Measure α) : Prop :=
  AEStronglyMeasurable f μ ∧ eLorentzNorm f p r μ < ∞

theorem MemLorentz.aestronglyMeasurable [TopologicalSpace ε] {f : α → ε} {p : ℝ≥0∞}
  (h : MemLorentz f p q μ) :
    AEStronglyMeasurable f μ :=
  h.1

lemma MemLorentz.aemeasurable [MeasurableSpace ε] [TopologicalSpace ε]
    [TopologicalSpace.PseudoMetrizableSpace ε] [BorelSpace ε]
    {f : α → ε} {p : ℝ≥0∞} (hf : MemLorentz f p q μ) :
    AEMeasurable f μ :=
  hf.aestronglyMeasurable.aemeasurable

end Lorentz

end MeasureTheory
