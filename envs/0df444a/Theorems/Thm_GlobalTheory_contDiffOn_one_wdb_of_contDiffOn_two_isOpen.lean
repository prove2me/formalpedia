-- Prove2me | Theorems.Thm_GlobalTheory_contDiffOn_one_wdb_of_contDiffOn_two_isOpen
-- name    : GlobalTheory.contDiffOn_one_wdb_of_contDiffOn_two_isOpen
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:14:28.167135+00:00
-- url     : https://prove2.me/theorems/77df4f65-e518-439a-8528-3003e75286bb
-- title:
--   Global Theory: cont Diff On one wdb of cont Diff On two is Open
-- statement:
--   The Global Theory construction uses the cont Diff On one wdb of cont Diff On two is Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOnComplexHessianOfContDiffOnTwo.lean#L8-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOnComplexHessianOfContDiffOnTwo.lean#L8-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnComplexHessianOfContDiffOnTwo
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
open GlobalTheory

theorem GlobalTheory.contDiffOn_one_wdb_of_contDiffOn_two_isOpen {n : ℕ} {U : Set (V n)} {g : V n → ℂ}
    (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U) (l : Fin n) :
    ContDiffOn ℝ 1 (wdb n l g) U := by sorry
