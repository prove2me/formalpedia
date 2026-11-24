-- Prove2me | Theorems.Thm_GlobalTheory_PluriTaylor_sum_re_im_eq
-- name    : GlobalTheory.PluriTaylor.sum_re_im_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:49:10.212153+00:00
-- url     : https://prove2.me/theorems/669fda41-6e3c-4fe7-9a3e-f42b871e57f9
-- title:
--   Pluri Taylor: sum re im eq
-- statement:
--   The Pluri Taylor construction uses the sum re im eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformTaylorBoundLeviPluriharmonicSplit.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformTaylorBoundLeviPluriharmonicSplit.lean#L23-L26

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformTaylorBoundLeviPluriharmonicSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
open GlobalTheory GlobalTheory.PluriTaylor
open Complex Set
variable {n : ℕ}

theorem GlobalTheory.PluriTaylor.sum_re_im_eq (w : V n) :
    (∑ k, ((w k).re • bas n k + (w k).im • (I • bas n k))) = w := by sorry
