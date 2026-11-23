-- Prove2me | Theorems.Thm_GlobalTheory_mem_normIntegers_iff
-- name    : GlobalTheory.mem_normIntegers_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:19:24.530798+00:00
-- url     : https://prove2.me/theorems/351aeb34-b829-486e-ba33-c2954d872a46
-- title:
--   Global Theory: mem norm Integers iff
-- statement:
--   The Global Theory construction uses the mem norm Integers iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L14-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
universe u

theorem GlobalTheory.mem_normIntegers_iff {C : Type*} [NormedField C] [IsUltrametricDist C] {x : C} :
    x ∈ normIntegers C ↔ ‖x‖ ≤ 1 := by sorry
