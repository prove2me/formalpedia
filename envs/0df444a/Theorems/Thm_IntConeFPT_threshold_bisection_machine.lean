-- Prove2me | Theorems.Thm_IntConeFPT_threshold_bisection_machine
-- name    : IntConeFPT.threshold_bisection_machine
-- status  : Open
-- author  : @ohnesorgefelix
-- created : 2026-11-25T11:53:26.782845+00:00
-- url     : https://prove2.me/theorems/5c848c1d-3fbe-46ee-b5cf-72199d0c8c3d
-- title:
--   Compiling monotone witnessed binary search with a uniform step bound
-- statement:
--   An arbitrary subroutine takes a word $x$ followed by an encoded index and returns a word, with the singleton zero meaning no. Suppose the yes answers are monotone on $[0,2B]$, where $B=2^{L^2+4L}$ and $L$ is the length of $x$. A search machine returns the original witness word at the least yes index, or zero if all answers are no. For a uniform bound $T$ on the promised query runs, its cost is polynomial in $L+T+2$, with no assumptions on the subroutine outside this range. This compilation claim concerns binary words and run bounds only, not geometry or objectives.
-- source:
--   Jansen, Ohnesorge and Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, https://arxiv.org/abs/2609.31328, §3.5, proof of Proposition 14, pp.16–17 (witnessed budget tests and binary search).

import Definitions.Def_IntConeFPT_Machine
import Definitions.Def_OnlineCRS_Combine_encNat
open OnlineCRS.Combine IntConeFPT

theorem IntConeFPT.threshold_bisection_machine (A : Machine) :
    ∃ d : ℕ, ∃ W : Machine, ∀ (x : List Sym) (a : ℕ → List Sym) (T : ℝ),
      let B := 2^(x.length^2+4*x.length)
      (∀ k ≤ 2*B, RunsWithin A (x ++ encNat k ++ [3]) (a k) T) →
      (∀ i j, i ≤ j → j ≤ 2*B → a i ≠ [0] → a j ≠ [0]) →
      ∃ k : ℕ, k ≤ 2*B ∧
        (a k = [0] → ∀ j ≤ 2*B, a j = [0]) ∧
        (a k ≠ [0] → ∀ j < k, a j = [0]) ∧
        RunsWithin W x (a k) ((x.length + T + 2 : ℝ)^d) := by sorry
