-- Prove2me | Theorems.Thm_GlobalTheory_DirichletTail_LFunction_eq_tsum_of_one_lt
-- name    : GlobalTheory.DirichletTail.LFunction_eq_tsum_of_one_lt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:48:38.932835+00:00
-- url     : https://prove2.me/theorems/96054ccc-fcdc-4699-9b1b-2f151cc229e6
-- title:
--   Dirichlet Tail: LFunction eq tsum of one lt
-- statement:
--   The Dirichlet Tail construction uses the LFunction eq tsum of one lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LFunctionEqTsumOfOneLt.lean#L171-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LFunctionEqTsumOfOneLt.lean#L171-L192

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

theorem GlobalTheory.DirichletTail.LFunction_eq_tsum_of_one_lt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) : LFunction χ s = ∑' n, term χ n s := by sorry
