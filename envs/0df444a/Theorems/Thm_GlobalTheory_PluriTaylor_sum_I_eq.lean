-- Prove2me | Theorems.Thm_GlobalTheory_PluriTaylor_sum_I_eq
-- name    : GlobalTheory.PluriTaylor.sum_I_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:48:47.580166+00:00
-- url     : https://prove2.me/theorems/5b771b06-f353-4e3a-9684-bece6fd9bb3a
-- title:
--   Pluri Taylor: sum I eq
-- statement:
--   The Pluri Taylor construction uses the sum I eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformTaylorBoundLeviPluriharmonicSplit.lean#L28-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformTaylorBoundLeviPluriharmonicSplit.lean#L28-L38

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

theorem GlobalTheory.PluriTaylor.sum_I_eq (w : V n) :
    (∑ k, ((w k).re • (I • bas n k) - (w k).im • bas n k)) = I • w := by sorry
