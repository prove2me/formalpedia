-- Prove2me | Theorems.Thm_GlobalTheory_PeriodNonempty_exists_diag_real
-- name    : GlobalTheory.PeriodNonempty.exists_diag_real
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:32:36.886799+00:00
-- url     : https://prove2.me/theorems/c2f80825-86a0-4bab-b396-458eb2890068
-- title:
--   Period Nonempty: exists diag real
-- statement:
--   The Period Nonempty construction uses the exists diag real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsEquivOfSumEq.lean#L82-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsEquivOfSumEq.lean#L82-L123

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodNonempty
noncomputable section

theorem GlobalTheory.PeriodNonempty.exists_diag_real {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] (J : W →ₗ[ℝ] W) (hJ : ∀ x, J (J x) = -x) (ρ : 𝓞 E →+* Module.End ℝ W) {g : ℕ}
    (ty : Fin g → (E →+* ℂ))
    (h : ∀ a, J ∘ₗ ρ a = ρ a ∘ₗ J ∧ LinearMap.trace ℝ W (ρ a) = 2 * (∑ i, ty i (a : E)).re ∧
      LinearMap.trace ℝ W (J ∘ₗ ρ a) = -2 * (∑ i, ty i (a : E)).im) :
    ∃ e : W ≃ₗ[ℝ] (Fin g → ℂ), (∀ v, e (J v) = Complex.I • e v) ∧
      ∀ a v i, e (ρ a v) i = ty i (a : E) * e v i := by sorry
