-- Prove2me | Theorems.Thm_GlobalTheory_SCV_span_scaledRealPoints
-- name    : GlobalTheory.SCV.span_scaledRealPoints
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:33:01.876873+00:00
-- url     : https://prove2.me/theorems/9afccfd1-33c9-4aa0-b588-9b50a29e3b52
-- title:
--   SCV: span scaled Real Points
-- statement:
--   The SCV construction uses the span scaled Real Points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EventuallyIteratedFDerivEqZeroOfRealSubspace.lean#L89-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EventuallyIteratedFDerivEqZeroOfRealSubspace.lean#L89-L103

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EventuallyIteratedFDerivEqZeroOfRealSubspace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter
open scoped Topology
open GlobalTheory GlobalTheory.SCV
variable {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℂ V]
omit [Fintype ι]

theorem GlobalTheory.SCV.span_scaledRealPoints {a : ℂ} (ha : a ≠ 0) :
    Submodule.span ℂ (scaledRealPoints ι a : Set (ι → ℂ)) = ⊤ := by sorry
