-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_tendsto_seriesEval
-- name    : GroundTheory.PAdicHodge.tendsto_seriesEval
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:47:11.306555+00:00
-- url     : https://prove2.me/theorems/7cddef6a-3c1a-458b-be70-2e7ef96bcda2
-- title:
--   PAdic Hodge: tendsto series Eval
-- statement:
--   The PAdic Hodge construction uses the tendsto series Eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRSeries.lean#L130-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRSeries.lean#L130-L138

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BdRSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open PowerSeries
variable {B : Type*} [CommRing B] (I : Ideal B)
variable [Algebra ℚ B]
variable [IsAdicComplete I B]
variable {I}

theorem GroundTheory.PAdicHodge.tendsto_seriesEval {z : B} (hz : z ∈ I) (f : ℚ⟦X⟧) :
    @Filter.Tendsto ℕ B (fun n => ∑ i ∈ Finset.range n, algebraMap ℚ B (coeff i f) * z ^ i)
      Filter.atTop (@nhds B I.adicTopology (seriesEval I z hz f)) := by sorry
