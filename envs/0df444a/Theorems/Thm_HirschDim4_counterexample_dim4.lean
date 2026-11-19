-- Prove2me | Theorems.Thm_HirschDim4_counterexample_dim4
-- name    : HirschDim4.counterexample_dim4
-- status  : Open
-- author  : @LG
-- created : 2026-11-16T22:53:17.243206+00:00
-- url     : https://prove2.me/theorems/e20210a9-5f06-4782-b7e4-9cb2d4396e1e
-- title:
--   The Hirsch conjecture fails in dimension $4$: a rational counterexample
-- statement:
--   **The Hirsch conjecture is false in dimension $4$.** There exist an integer $n$, an integer matrix $A\in\mathbb{Z}^{n\times 4}$ and an integer vector $b\in\mathbb{Z}^n$ such that the polytope
--   $$P=\{x\in\mathbb{R}^4:Ax\le b\}$$
--   is nonempty, bounded and full-dimensional, its $n$ rows are exactly its facets (each row irredundant), and its combinatorial diameter is strictly greater than $n-4$:
--   $$\operatorname{diam}G(P)>n-4.$$
--   Here $G(P)$ is the vertex–edge graph of $P$ and the diameter is the largest graph distance between two vertices. This is the smallest open dimension of the Hirsch conjecture: it is known to hold for $d\le 3$ and for all $4$-polytopes with at most $12$ facets, so any counterexample has $n\ge 13$. Integer data make $P$ a rational polytope, as the benchmark requires; a solution should exhibit explicit $A,b$ (and may compute the vertices).
--
--   **Formalization Note.** `IsFacetPresentation` encodes full-dimensionality (nonempty interior) plus irredundancy of every row, which for bounded $P$ makes the rows bijective with the facets. `IsNonHirsch a b` is `¬ Hirsch.DiamLE (Hpoly a b) (n-4)`, i.e. diameter $>n-4$; since $n\ge 5$ is forced, $n-4$ is genuine natural-number subtraction. The statement is equivalent to plain existence of a bounded $4$-dimensional counterexample, because every combinatorial type of polytope admits a rational realization.
-- source:
--   Epoch AI, FrontierMath: Open Problems, The Hirsch Conjecture in Dimension 4, https://epoch.ai/frontiermath/open-problems/hirsch-conjecture (Prompt: explicit rational polytope in R^4 with diameter > n-4). Context: F. Santos, Annals of Math. 176 (2012), 383-412, https://doi.org/10.4007/annals.2012.176.1.7.

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Definitions.Def_SantosHirsch_Counter_Setting
import Definitions.Def_HirschDim4_Setting

open scoped RealInnerProductSpace

namespace HirschDim4

theorem counterexample_dim4 :
    ∃ (n : ℕ) (A : Matrix (Fin n) (Fin 4) ℤ) (b : Fin n → ℤ),
      (Hirsch.Hpoly (intRows A) (intRhs b)).Nonempty ∧
      Bornology.IsBounded (Hirsch.Hpoly (intRows A) (intRhs b)) ∧
      SantosHirsch.Counter.IsFacetPresentation (intRows A) (intRhs b) ∧
      SantosHirsch.Counter.IsNonHirsch (intRows A) (intRhs b) := by sorry

end HirschDim4
