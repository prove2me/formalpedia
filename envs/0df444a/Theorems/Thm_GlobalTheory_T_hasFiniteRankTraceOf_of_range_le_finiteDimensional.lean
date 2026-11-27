-- Prove2me | Theorems.Thm_GlobalTheory_T_hasFiniteRankTraceOf_of_range_le_finiteDimensional
-- name    : GlobalTheory.T.hasFiniteRankTraceOf_of_range_le_finiteDimensional
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-27T05:57:45.316076+00:00
-- url     : https://prove2.me/theorems/620823b4-f8b5-5075-94f0-945bc072d6af
-- title:
--   T: has Finite Rank Trace Of of range le finite Dimensional
-- statement:
--   The T construction uses the has Finite Rank Trace Of of range le finite Dimensional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasFiniteRankTraceOfOfRangeLeFiniteDimensionalStatement.lean#L6-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasFiniteRankTraceOfOfRangeLeFiniteDimensionalStatement.lean#L6-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasFiniteRankTraceOfOfRangeLeFiniteDimensional
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IwahoriDoubleCosets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasFiniteRankTraceOfOfRangeLeFiniteDimensionalStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hasFiniteRankTraceOf_of_range_le_finiteDimensional : ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (T : X →ₗ[ℂ] X) (Z : Submodule ℂ X)
    [FiniteDimensional ℂ Z] (hT : LinearMap.range T ≤ Z),
    GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace T (LinearMap.trace ℂ Z (T.restrict (p := Z) (q := Z)
      fun x _ => hT (LinearMap.mem_range_self T x))) := by sorry
