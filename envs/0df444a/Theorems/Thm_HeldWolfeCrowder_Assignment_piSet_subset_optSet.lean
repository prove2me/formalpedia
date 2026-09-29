-- Prove2me | Theorems.Thm_HeldWolfeCrowder_Assignment_piSet_subset_optSet
-- name    : HeldWolfeCrowder.Assignment.piSet_subset_optSet
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:54:05.780634+00:00
-- url     : https://prove2.me/theorems/23f88ebe-91b5-4887-8283-d5823c2421d1
-- title:
--   Eq. (3.6) — the set Π is open, convex, has v = 0, and lies in the optimal set
-- statement:
--   Let $A=(a_{ir})$ be a real $n\times n$ cost matrix, $w$ the dual function (3.3), and $\sigma$ an optimal one-to-one assignment. Let
--
--   $$\Pi=\{\pi\in\mathbb R^n : a_{ir}-\pi_i>a_{\sigma(r)\,r}-\pi_{\sigma(r)} \text{ for every job } r \text{ and every man } i\ne\sigma(r)\}.$$
--
--   Then:
--   1. for $\pi\in\Pi$, the minimum in the representation (3.4), $\min_A\{c_A+\sum_i\pi_i(v_A)_i\}$, is attained only at the assignment $A=\sigma$ (every assignment $A$ with $c_A+\sum_i\pi_i(v_A)_i\le c_\sigma+\sum_i\pi_i(v_\sigma)_i$ equals $\sigma$);
--   2. $v_\sigma=0$, so the subgradient $v(\pi)$ of $w$ at every $\pi\in\Pi$ is $0$;
--   3. $\Pi$ is convex and open;
--   4. $\Pi$ is contained in the optimal set $\{\pi : w(\pi')\le w(\pi)\ \forall\pi'\}$ of (3.3).
--
--   Together with (3.5), which makes $\Pi$ nonempty, this gives an open nonempty subset of the optimal set, which is how Theorem 3.1 follows.
--
--   **Formalization Note** The page prints the condition of (3.6) as "for all $r$, $i\ne r$"; the statement uses $i\ne\sigma(r)$, which is what the argument requires. The page's parenthetical claim that $\Pi$ is exactly the interior of the optimal set is not part of this statement.
-- source:
--   Held, Wolfe & Crowder, Validation of subgradient optimization, Math. Programming 6 (1974), p. 70, Eq. (3.6) and the sentence following it (proof of Theorem 3.1)

import Mathlib
import Definitions.Def_HeldWolfeCrowder_Assignment_Setting

namespace HeldWolfeCrowder.Assignment

/-- Held–Wolfe–Crowder (1974), p. 70, Eq. (3.6): for an optimal one-to-one assignment `σ`, on
the set `Π` of (3.6) the minimum in the representation (3.4) is attained only at the assignment
`σ`, whose vector `v_σ` is `0`; `Π` is convex and open, and it is contained in the optimal set
of (3.3). -/
theorem piSet_subset_optSet {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ)
    (σ : Equiv.Perm (Fin n)) (hσ : IsOptimalAssignment a σ) :
    (∀ π ∈ PiSet a σ, ∀ A : Fin n → Fin n,
        assignCost a A + ∑ i, π i * assignVec A i ≤ assignCost a σ + ∑ i, π i * assignVec σ i →
          A = σ) ∧
      (∀ i, assignVec σ i = 0) ∧
      Convex ℝ (PiSet a σ) ∧ IsOpen (PiSet a σ) ∧ PiSet a σ ⊆ optSet a := by sorry

end HeldWolfeCrowder.Assignment
