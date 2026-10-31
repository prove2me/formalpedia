-- Prove2me | Theorems.Thm_LowRankIndicator_lp7_unbounded_direction
-- name    : LowRankIndicator.lp7_unbounded_direction
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:18:29.36985+00:00
-- url     : https://prove2.me/theorems/338b2346-f657-4d23-ae2c-c77048b62717
-- title:
--   Proof of Theorem 1, p.7 — if (7) is unbounded, it has an improving feasible direction $d$ with $Ad=0$
-- statement:
--   Let $A$ be a $k\times n$ real matrix, $\bar x,\beta\in\mathbb R^n$, and suppose that $\beta^\top x$ is unbounded above on the feasible region of the linear program (7). Then there is a direction $d\in\mathbb R^n$ with
--
--   $$Ad=0,\qquad \bar x_id_i\ge0\ \ \forall i\in\operatorname{supp}(\bar x),\qquad d_i=0\ \ \forall i\notin\operatorname{supp}(\bar x),\qquad \beta^\top d>0.$$
--
--   This is the case that produces a ray of $R$ along which the support function is $+\infty$.
--
--   Differences from the source:
--   - generalization: objective (αₓ + αₜc)⊤x and x̄ from a point of Q → arbitrary β and arbitrary x̄; reason: the paper's case is β = αₓ + αₜc with x̄ from Q
--   - encoding: v∗ = +∞ → `∀ M : ℝ, ∃ x ∈ feas7 A xbar, M < β ⬝ᵥ x`; reason: this is what the value +∞ of a supremum over a nonempty set means
-- source:
--   Han & Gómez, Compact Extended Formulations for Low-Rank Functions with Indicator Variables, arXiv:2110.14884v2, proof of Theorem 1, (7) and "If v∗ = +∞", p.7.

import Mathlib
import Definitions.Def_LowRankIndicator_FeasibleSet7

open scoped Matrix

namespace LowRankIndicator

/-- Han & Gómez, arXiv:2110.14884v2, proof of Theorem 1, p.7, "If v∗ = +∞, then there exists a
feasible direction d such that Ad = 0 and (αx + αtc)⊤d > 0.": an unbounded linear program (7) has
an improving feasible direction.

**Formalization Note.** The objective vector `β` is arbitrary (the paper's is `αx + αt c`), and
`xbar` need not come from a point of `Q`. `v∗ = +∞` is `∀ M : ℝ, ∃ x ∈ feas7 A xbar, M < β ⬝ᵥ x`.
"Feasible direction" spells out the sign and zero constraints of (7) for `d`. -/
theorem lp7_unbounded_direction {n k : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (xbar β : Fin n → ℝ)
    (hunbounded : ∀ M : ℝ, ∃ x ∈ feas7 A xbar, M < β ⬝ᵥ x) :
    ∃ d : Fin n → ℝ, A.mulVec d = 0 ∧ (∀ i, xbar i ≠ 0 → 0 ≤ xbar i * d i) ∧
      (∀ i, xbar i = 0 → d i = 0) ∧ 0 < β ⬝ᵥ d := by sorry

end LowRankIndicator
