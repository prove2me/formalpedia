-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_mk_seriesEval
-- name    : GroundTheory.PAdicHodge.mk_seriesEval
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:46:39.440809+00:00
-- url     : https://prove2.me/theorems/938e86a6-0068-4ca3-96d8-41684eab9615
-- title:
--   PAdic Hodge: mk series Eval
-- statement:
--   The PAdic Hodge construction uses the mk series Eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRSeries.lean#L116-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRSeries.lean#L116-L124

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

theorem GroundTheory.PAdicHodge.mk_seriesEval {z : B} (hz : z ∈ I) (f : ℚ⟦X⟧) (n : ℕ) :
    Ideal.Quotient.mk (I ^ n) (seriesEval I z hz f) =
      Ideal.Quotient.mk (I ^ n) (∑ i ∈ Finset.range n, algebraMap ℚ B (coeff i f) * z ^ i) := by sorry
