-- Prove2me | Theorems.Thm_GlobalTheory_LOneLower_summable_inv_exp
-- name    : GlobalTheory.LOneLower.summable_inv_exp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:21.829817+00:00
-- url     : https://prove2.me/theorems/73121da6-d51a-42d7-9942-d10eb8abc3a3
-- title:
--   LOne Lower: summable inv exp
-- statement:
--   The LOne Lower construction uses the summable inv exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLeNormLFunctionOne.lean#L240-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLeNormLFunctionOne.lean#L240-L254

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLeNormLFunctionOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
open scoped ComplexOrder
open GlobalTheory GlobalTheory.LOneLower

theorem GlobalTheory.LOneLower.summable_inv_exp {α : ℝ} (hα : 0 < α) :
    Summable fun d : ℕ => (Real.exp (((d + 1 : ℕ) : ℝ) * α) - 1)⁻¹ := by sorry
