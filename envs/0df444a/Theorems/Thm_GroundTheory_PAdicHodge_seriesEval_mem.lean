-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_seriesEval_mem
-- name    : GroundTheory.PAdicHodge.seriesEval_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:47:14.610779+00:00
-- url     : https://prove2.me/theorems/664978a1-7a7a-4d0e-8049-1e6bcf7f3c4e
-- title:
--   PAdic Hodge: series Eval mem
-- statement:
--   The PAdic Hodge construction uses the series Eval mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRSeries.lean#L150-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRSeries.lean#L150-L154

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

theorem GroundTheory.PAdicHodge.seriesEval_mem {z : B} (hz : z ∈ I) {f : ℚ⟦X⟧} (hf : constantCoeff f = 0) :
    seriesEval I z hz f ∈ I := by sorry
