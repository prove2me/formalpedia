-- Prove2me | Theorems.Thm_MunkresAlg_Assignment_stronger_result
-- name    : MunkresAlg.Assignment.stronger_result
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:11:01.94634+00:00
-- url     : https://prove2.me/theorems/585fd87d-6fdb-4397-b484-dfaf09151c9d
-- title:
--   §1, the stronger result, p. 35 — if n_{k+1} = n_k, Step 2 does not occur and Step 3 is begun with more horizontal covered lines
-- statement:
--   Let $A$ be a real $n\times n$ matrix, let $s$ be a state reachable by Munkres' algorithm from $A$ that is at Step 3 with matrix $A_k$, and let $s_1$ be the state after the Step 3 move, with matrix $A_{k+1}$. Suppose $n_{k+1}=n_k$, where $n_i$ is the maximal number of independent zeros of $A_i$. Let $s_2$ be any state reached from $s_1$ by moves made in Step 1 such that $s_2$ is no longer in Step 1. Then
--
--   1. $s_2$ is at Step 3 (Step 2 does not occur), and
--   2. every covered row of $s$ is a covered row of $s_2$, and
--   $$
--   \#\{\text{covered rows of } s_2\} > \#\{\text{covered rows of } s\}.
--   $$
--
--   Covered rows are the paper's *horizontal covered lines*. This is the progress measure that replaces the integrality assumption in the proof of finiteness.
-- source:
--   Munkres, Algorithms for the assignment and transportation problems, J. SIAM 5 (1957), p. 35, §1, the stronger result

import Mathlib
import Definitions.Def_MunkresAlg_Assignment_Basic
import Definitions.Def_MunkresAlg_Assignment_Algorithm

namespace MunkresAlg.Assignment

/-- §1, the stronger result, p. 35: if the Step 3 transformation from `A_k = s.A` to
`A_{k+1} = s₁.A` leaves the maximal number of independent zeros unchanged, then every way of
continuing Step 1 from `s₁` until Step 1 is left goes to Step 3 (Step 2 does not occur), and
Step 3 is begun with more covered rows (horizontal lines) than at `s`, every covered row of `s`
still being covered. -/
theorem stronger_result {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s s₁ : State n)
    (hs : Reachable A s) (hph : s.phase = Phase.step3) (h1 : Step s s₁)
    (heq : maxIndepZeros s₁.A = maxIndepZeros s.A) :
    ∀ s₂ : State n, Relation.ReflTransGen Step1Move s₁ s₂ → s₂.phase ≠ Phase.step1 →
      s₂.phase = Phase.step3 ∧ s.rowCov ⊆ s₂.rowCov ∧ s.rowCov.card < s₂.rowCov.card := by sorry

end MunkresAlg.Assignment
