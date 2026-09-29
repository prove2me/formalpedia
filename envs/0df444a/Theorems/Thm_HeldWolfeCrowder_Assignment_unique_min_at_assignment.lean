-- Prove2me | Theorems.Thm_HeldWolfeCrowder_Assignment_unique_min_at_assignment
-- name    : HeldWolfeCrowder.Assignment.unique_min_at_assignment
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:53:39.172792+00:00
-- url     : https://prove2.me/theorems/68936040-6e7b-4a64-92e5-1ddbc4e5a9b5
-- title:
--   Eq. (3.5) — a unique optimal assignment gives optimal prices with a unique cheapest man for every job
-- statement:
--   Let $A=(a_{ir})$ be a real $n\times n$ cost matrix and $w$ the dual function (3.3). Suppose the assignment problem has a unique optimal one-to-one assignment $\sigma$: $\sigma$ is optimal, and every optimal permutation equals $\sigma$. Then there is a price vector $\bar\pi\in\mathbb R^n$ that maximizes $w$ and such that
--
--   $$\text{for each job } r,\ \ \min_s\,[a_{sr}-\bar\pi_s] \text{ is attained only at } s=\sigma(r),$$
--
--   that is, $a_{\sigma(r)\,r}-\bar\pi_{\sigma(r)}<a_{sr}-\bar\pi_s$ for every job $r$ and every man $s\neq\sigma(r)$.
--
--   In the paper this is the consequence of strict complementary slackness for the pair (3.1)–(3.2) when (3.1) has a unique solution, and it shows that the set $\Pi$ of (3.6) is nonempty.
-- source:
--   Held, Wolfe & Crowder, Validation of subgradient optimization, Math. Programming 6 (1974), p. 70, Eq. (3.5) (proof of Theorem 3.1)

import Mathlib
import Definitions.Def_HeldWolfeCrowder_Assignment_Setting

namespace HeldWolfeCrowder.Assignment

/-- Held–Wolfe–Crowder (1974), p. 70, Eq. (3.5): if `σ` is the unique optimal one-to-one
assignment, there is an optimal `π̄` for (3.3) such that, for each job `r`, the minimum
`min_s [a_{sr} − π̄_s]` is attained only at the man `s = σ(r)`. -/
theorem unique_min_at_assignment {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ)
    (σ : Equiv.Perm (Fin n)) (hσ : IsOptimalAssignment a σ)
    (huniq : ∀ τ : Equiv.Perm (Fin n), IsOptimalAssignment a τ → τ = σ) :
    ∃ πbar : Fin n → ℝ, πbar ∈ optSet a ∧
      ∀ r s : Fin n, s ≠ σ r → a (σ r) r - πbar (σ r) < a s r - πbar s := by sorry

end HeldWolfeCrowder.Assignment
