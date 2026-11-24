-- Prove2me | Theorems.Thm_GlobalTheory_PeriodNonempty_exists_diag
-- name    : GlobalTheory.PeriodNonempty.exists_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:24.172288+00:00
-- url     : https://prove2.me/theorems/b4cca4ef-b262-4333-8fd5-20a84bc9c3d0
-- title:
--   Period Nonempty: exists diag
-- statement:
--   The Period Nonempty construction uses the exists diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsEquivOfSumEq.lean#L42-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsEquivOfSumEq.lean#L42-L70

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

theorem GlobalTheory.PeriodNonempty.exists_diag {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ρ : 𝓞 E →+* Module.End ℂ W) {g : ℕ} (ty : Fin g → (E →+* ℂ))
    (h : ∀ a, LinearMap.trace ℂ W (ρ a) = ∑ i, ty i (a : E)) :
    ∃ e : W ≃ₗ[ℂ] (Fin g → ℂ), ∀ a v i, e (ρ a v) i = ty i (a : E) * e v i := by sorry
