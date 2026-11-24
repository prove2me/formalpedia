-- Prove2me | Theorems.Thm_GlobalTheory_DirichletTail_norm_LFunction_sub_sum_le
-- name    : GlobalTheory.DirichletTail.norm_LFunction_sub_sum_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:48:37.628086+00:00
-- url     : https://prove2.me/theorems/f1d91210-556c-47bf-8726-5a67ca5f667f
-- title:
--   Dirichlet Tail: norm LFunction sub sum le
-- statement:
--   The Dirichlet Tail construction uses the norm LFunction sub sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LFunctionEqTsumOfOneLt.lean#L226-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LFunctionEqTsumOfOneLt.lean#L226-L267

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

theorem GlobalTheory.DirichletTail.norm_LFunction_sub_sum_le :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ s : ℂ, 0 < s.re → ∀ N : ℕ, 1 ≤ N →
      ‖LFunction χ s - ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-s)‖
        ≤ 2 * q * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) := by sorry
