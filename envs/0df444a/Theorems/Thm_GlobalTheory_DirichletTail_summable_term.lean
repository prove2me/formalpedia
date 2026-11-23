-- Prove2me | Theorems.Thm_GlobalTheory_DirichletTail_summable_term
-- name    : GlobalTheory.DirichletTail.summable_term
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:11.237319+00:00
-- url     : https://prove2.me/theorems/011d6e69-4a4d-4a3f-8786-891ba1801ab2
-- title:
--   Dirichlet Tail: summable term
-- statement:
--   The Dirichlet Tail construction uses the summable term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LFunctionEqTsumOfOneLt.lean#L156-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LFunctionEqTsumOfOneLt.lean#L156-L162

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionEqTsumOfOneLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.DirichletTail
open Filter Topology

theorem GlobalTheory.DirichletTail.summable_term {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) : Summable (fun n => term χ n s) := by sorry
