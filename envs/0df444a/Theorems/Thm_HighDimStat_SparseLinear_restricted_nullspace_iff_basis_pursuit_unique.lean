-- Prove2me | Theorems.Thm_HighDimStat_SparseLinear_restricted_nullspace_iff_basis_pursuit_unique
-- name    : HighDimStat.SparseLinear.restricted_nullspace_iff_basis_pursuit_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T23:09:15.64299+00:00
-- url     : https://prove2.me/theorems/558bbbb3-4f92-4bf3-a9c2-c0f4c89c1221
-- title:
--   Restricted nullspace property is equivalent to exact basis pursuit recovery
-- statement:
--   **Theorem 7.8.** Exact recovery by the basis pursuit linear program (7.9) for every sparse
--   vector is equivalent to a purely deterministic geometric property of the design matrix
--   $X$: the restricted nullspace property.
--
--   For $X \in \mathbb R^{n\times d}$ and $S \subseteq \{1,\dots,d\}$, the following are
--   equivalent:
--
--   $$
--   \text{(a)}\quad \forall \theta^* \in \mathbb R^d \text{ with } \mathrm{HasSupport}(\theta^*,
--   S),\ \forall \hat\theta,\ \hat\theta \text{ solves (7.9) for } (X, X\theta^*)
--   \Rightarrow \hat\theta = \theta^*;
--   $$
--   $$
--   \text{(b)}\quad X \text{ satisfies the restricted nullspace property with respect to } S.
--   $$
--
--   This is the chapter's foundational recovery result: it reduces the analysis of a convex
--   program's exactness to a linear-algebraic condition on $X$ alone, with no reference to any
--   particular optimization algorithm.
--
--   **Formalization Note** Direction (a) is written as "every optimal solution of (7.9) with
--   $y=X\theta^*$ equals $\theta^*$," which packages both existence (implicit, since $\theta^*$
--   itself is always feasible and — under (b) — the unique optimum) and uniqueness of the
--   solution, exactly matching the book's phrase "has unique solution $\hat\theta = \theta^*$."
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 202 (PDF p. 222), Theorem 7.8

import Mathlib
import Definitions.Def_HighDimStat_SparseLinear_HasSupport
import Definitions.Def_HighDimStat_SparseLinear_RestrictedNullspaceProperty
import Definitions.Def_HighDimStat_SparseLinear_IsBasisPursuitSolution

namespace HighDimStat.SparseLinear

/-- **Theorem 7.8**, Wainwright, *High-Dimensional Statistics* (2019), p. 202. The following two
properties are equivalent: (a) for any vector `θ* ∈ ℝ^d` with support `S`, the basis pursuit
program (7.9) applied with `y = Xθ*` has unique solution `θhat = θ*`; (b) the matrix `X`
satisfies the restricted nullspace property with respect to `S`. -/
theorem restricted_nullspace_iff_basis_pursuit_unique {n d : ℕ}
    (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) :
    (∀ θstar : Fin d → ℝ, HasSupport θstar S →
      ∀ θhat : Fin d → ℝ, IsBasisPursuitSolution X (X.mulVec θstar) θhat → θhat = θstar)
    ↔ RestrictedNullspaceProperty X S := by sorry

end HighDimStat.SparseLinear
