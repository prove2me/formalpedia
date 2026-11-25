-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_seriesEval_sub_sum_mem
-- name    : GroundTheory.PAdicHodge.seriesEval_sub_sum_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:41.965486+00:00
-- url     : https://prove2.me/theorems/7e346680-92e3-4399-bc46-5e8f74bcff8e
-- title:
--   PAdic Hodge: series Eval sub sum mem
-- statement:
--   The PAdic Hodge construction uses the series Eval sub sum mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRSeries.lean#L126-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRSeries.lean#L126-L128

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

theorem GroundTheory.PAdicHodge.seriesEval_sub_sum_mem {z : B} (hz : z ∈ I) (f : ℚ⟦X⟧) (n : ℕ) :
    seriesEval I z hz f - ∑ i ∈ Finset.range n, algebraMap ℚ B (coeff i f) * z ^ i ∈ I ^ n := by sorry
