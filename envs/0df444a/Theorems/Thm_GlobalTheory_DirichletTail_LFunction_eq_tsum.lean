-- Prove2me | Theorems.Thm_GlobalTheory_DirichletTail_LFunction_eq_tsum
-- name    : GlobalTheory.DirichletTail.LFunction_eq_tsum
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:48:46.722396+00:00
-- url     : https://prove2.me/theorems/d5cd25a3-6089-4d0e-abe5-9d83b4e801ff
-- title:
--   Dirichlet Tail: LFunction eq tsum
-- statement:
--   The Dirichlet Tail construction uses the LFunction eq tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LFunctionEqTsumOfOneLt.lean#L194-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LFunctionEqTsumOfOneLt.lean#L194-L224

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

theorem GlobalTheory.DirichletTail.LFunction_eq_tsum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) : LFunction χ s = ∑' n, term χ n s := by sorry
