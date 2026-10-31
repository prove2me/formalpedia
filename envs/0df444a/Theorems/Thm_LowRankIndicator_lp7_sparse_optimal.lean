-- Prove2me | Theorems.Thm_LowRankIndicator_lp7_sparse_optimal
-- name    : LowRankIndicator.lp7_sparse_optimal
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:18:49.325994+00:00
-- url     : https://prove2.me/theorems/d8dc1163-e5ef-4c57-91dd-1b9f6771542e
-- title:
--   Proof of Theorem 1, p.7 — if (7) has a finite value, it has an optimal extreme point $x^*$ with $|\operatorname{supp}(x^*)|\le k$
-- statement:
--   Let $A$ be a $k\times n$ real matrix, $\bar x,\beta\in\mathbb R^n$, and suppose that $\beta^\top x$ is bounded above on the feasible region $F$ of the linear program (7). Then there is an extreme point $x^*$ of $F$ that maximizes $\beta^\top x$ over $F$ and satisfies
--
--   $$|\operatorname{supp}(x^*)|\le k .$$
--
--   This is the step where low rank enters: the number of nonzero entries of an optimal solution is bounded by the number of rows of $A$.
--
--   Differences from the source:
--   - generalization: objective (αₓ + αₜc)⊤x and x̄ from a point of Q → arbitrary β and arbitrary x̄; reason: the paper's case is β = αₓ + αₜc with x̄ from Q
--   - reading: "a pointed polytope" → the feasible region is not assumed bounded; reason: (7) may be an unbounded polyhedron with finite value, and the paper's argument only uses that it is pointed
--   - encoding: v∗ finite → `BddAbove` of the objective values on the feasible region; reason: the region contains x̄, so the supremum is finite exactly when it is bounded above
-- source:
--   Han & Gómez, Compact Extended Formulations for Low-Rank Functions with Indicator Variables, arXiv:2110.14884v2, proof of Theorem 1, "If v∗ is finite", p.7.

import Mathlib
import Definitions.Def_LowRankIndicator_Sets
import Definitions.Def_LowRankIndicator_FeasibleSet7

open scoped Matrix

namespace LowRankIndicator

/-- Han & Gómez, arXiv:2110.14884v2, proof of Theorem 1, p.7, "If v∗ is finite, there exists an
optimal solution x∗ to (7). Moreover, x∗ can be taken as an extreme point of the feasible region
… Namely, x∗ satisfies | supp(x∗)| ≤ k.": a linear program (7) with a finite value has an optimal
extreme point whose support has at most `k` elements, `k` being the number of rows of `A`.

**Formalization Note.** The objective vector `β` is arbitrary (the paper's is `αx + αt c`), and
`xbar` need not come from a point of `Q`. "`v∗` is finite" is `BddAbove` of the objective values;
the feasible region is nonempty because it contains `xbar`. The paper's "pointed polytope" is a
pointed polyhedron, not necessarily bounded. -/
theorem lp7_sparse_optimal {n k : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (xbar β : Fin n → ℝ)
    (hfinite : BddAbove ((fun x => β ⬝ᵥ x) '' feas7 A xbar)) :
    ∃ xstar ∈ (feas7 A xbar).extremePoints ℝ,
      (∀ x ∈ feas7 A xbar, β ⬝ᵥ x ≤ β ⬝ᵥ xstar) ∧ (supp xstar).card ≤ k := by sorry

end LowRankIndicator
