-- Prove2me | Theorems.Thm_IntMul_FlatRecursiveEvaluation_kappa_bound_of_evaluations
-- name    : IntMul.FlatRecursiveEvaluation.kappa_bound_of_evaluations
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T03:49:36.290246+00:00
-- url     : https://prove2.me/theorems/0e2be3d5-466d-4a54-b58f-524128775e8c
-- title:
--   Exact campaign kappa bound from one real compiled recursive body
-- statement:
--   Let M be one fixed finite body machine with a fixed finite set of request labels and resume controls, and let κ≤1. Suppose every pair of n-bit inputs, for every positive n, has a finite recursive evaluation returning the exact 2n-bit product. Suppose further that there are C>0 and n₀ such that for n≥n₀ those evaluations have completely charged physical budgets at most C n L(n)^(1−κ), where L(n)=max(ceil(log₂ n),1). Then the campaign predicate KappaBound(κ) holds: one deterministic multitape Turing machine, with a fixed finite alphabet and exactly M.k+3 tapes independent of input size and recursion depth, computes the exact product at every positive input length and has eventual worst-case time O(n L(n)^(1−κ)). Its actual native input/output overhead is at most 18n+23 steps beyond the evaluation budget, and the eventual constant may be taken to be C+41. Pointwise finite evaluation totality is sufficient; no separate uniform early-size clock bound is assumed. This is a compiler-to-campaign interface theorem. Constructing a fast body and proving the charged evaluation budget remain mathematical implementation obligations.
-- source:
--   Original complete actual-machine compiler interface to the integer-multiplication kappa predicate. Written by Codex.

import Theorems.Thm_IntMul_FlatRecursiveEvaluation_native_evaluates_correct
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

open IntMul IntMul.FlatRecursiveEvaluation IntMul.TrackedBankPreparation

theorem IntMul.FlatRecursiveEvaluation.kappa_bound_of_evaluations (M : MultitapeTM) (labels : ℕ)
    (request : M.K → Option (Fin labels)) (resume : Fin labels → M.K)
    (κ : ℝ) (hκ : κ ≤ 1)
    (total : ∀ width : ℕ, 1 ≤ width →
      ∀ x y : List Bool, x.length=width → y.length=width →
        ∃ budget : ℕ,
          Evaluates M labels request resume (initialExtent M x y) (M.initCfg x y) []
            (bin (2*width) (val x*val y)) budget)
    (C : ℝ) (hC : 0 < C) (threshold : ℕ)
    (fast : ∀ width : ℕ, threshold ≤ width → 1 ≤ width →
      ∀ x y : List Bool, x.length=width → y.length=width →
        ∃ budget : ℕ, (budget:ℝ) ≤ C*(width:ℝ)*((lg width:ℝ)^(1-κ)) ∧
          Evaluates M labels request resume (initialExtent M x y) (M.initCfg x y) []
            (bin (2*width) (val x*val y)) budget) :
    KappaBound κ := by sorry
