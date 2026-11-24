-- Prove2me | Theorems.Thm_GlobalTheory_apply_add_intCast_vec_of_unit_periods
-- name    : GlobalTheory.apply_add_intCast_vec_of_unit_periods
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:19.667424+00:00
-- url     : https://prove2.me/theorems/3b9acae4-5c81-4252-8c03-6ddc65c1b071
-- title:
--   Global Theory: apply add int Cast vec of unit periods
-- statement:
--   The Global Theory construction uses the apply add int Cast vec of unit periods property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/FourierCoeffUnitCubeTranslateOfEntirePeriodic.lean#L11-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/FourierCoeffUnitCubeTranslateOfEntirePeriodic.lean#L11-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EventuallyIteratedFDerivEqZeroOfRealSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ShiftSingleInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology MeasureTheory
open scoped BigOperators Real
open GlobalTheory

theorem GlobalTheory.apply_add_intCast_vec_of_unit_periods {ι R E : Type*} [Fintype ι] [DecidableEq ι]
    [Ring R] {F : (ι → R) → E} (hF : ∀ (i : ι) x, F (x + Pi.single i 1) = F x)
    (n : ι → ℤ) (x : ι → R) : F (x + fun i => (n i : R)) = F x := by sorry
