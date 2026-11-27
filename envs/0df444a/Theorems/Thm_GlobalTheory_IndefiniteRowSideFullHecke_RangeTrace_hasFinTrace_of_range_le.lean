-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_RangeTrace_hasFinTrace_of_range_le
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace.hasFinTrace_of_range_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-27T05:56:31.422928+00:00
-- url     : https://prove2.me/theorems/ea559c33-5dac-5b39-a4b0-3b1d158869de
-- title:
--   Range Trace: has Fin Trace of range le
-- statement:
--   The Range Trace construction uses the has Fin Trace of range le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasFiniteRankTraceOfOfRangeLeFiniteDimensional.lean#L6-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasFiniteRankTraceOfOfRangeLeFiniteDimensional.lean#L6-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IwahoriDoubleCosets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasFiniteRankTraceOfOfRangeLeFiniteDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace

theorem GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace.hasFinTrace_of_range_le (X : Type) [AddCommGroup X] [Module ℂ X] (T : X →ₗ[ℂ] X)
    (Z : Submodule ℂ X) [FiniteDimensional ℂ Z] (hT : LinearMap.range T ≤ Z) :
    GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace T (LinearMap.trace ℂ Z (T.restrict (p := Z) (q := Z)
      fun x _ => hT (LinearMap.mem_range_self T x))) := by sorry
