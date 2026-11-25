-- Prove2me | Theorems.Thm_GlobalTheory_OfPeriod_exists_diag
-- name    : GlobalTheory.OfPeriod.exists_diag
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:36:03.485028+00:00
-- url     : https://prove2.me/theorems/fc3a345c-d71c-4078-96ea-e9d6496eee22
-- title:
--   Of Period: exists diag
-- statement:
--   The Of Period construction uses the exists diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FinrankHomComplex.lean#L189-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FinrankHomComplex.lean#L189-L215

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FinrankHomComplex
import Theorems.Thm_GlobalTheory_PeriodNonempty_exists_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OfPeriod
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
open Complex
variable {W : Type} [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W]
variable {S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ} {R : Submodule ℝ W}
open NumberField

theorem GlobalTheory.OfPeriod.exists_diag {E : Type} [Field E] [NumberField E] (U : Type) [AddCommGroup U] [Module ℂ U]
    [FiniteDimensional ℂ U] (σ : 𝓞 E →+* Module.End ℂ U) :
    ∃ (n : ℕ) (k : U ≃ₗ[ℂ] (Fin n → ℂ)) (F : 𝓞 E →+* Module.End ℂ (Fin n → ℂ)),
      (∃ ty : Fin n → (E →+* ℂ), ∀ a z i, F a z i = ty i (a : E) * z i) ∧ ∀ a u, k (σ a u) = F a (k u) := by sorry
