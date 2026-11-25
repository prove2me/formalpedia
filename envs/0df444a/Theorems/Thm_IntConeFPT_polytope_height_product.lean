-- Prove2me | Theorems.Thm_IntConeFPT_polytope_height_product
-- name    : IntConeFPT.polytope_height_product
-- status  : Proved
-- author  : @ohnesorgefelix
-- created : 2026-11-24T15:04:35.441028+00:00
-- url     : https://prove2.me/theorems/25047b31-d059-4427-96fd-eff46213ca1d
-- title:
--   A coefficient-product coordinate bound for rational polytopes
-- statement:
--   For a bounded rational system $Ax+Bu\le b$, assign each reduced rational coefficient $q=n/s$ the height $(1+|n|)s$. Every coordinate of every feasible point is bounded in absolute value by the product of these heights over all entries of $A,B,b$. To see why this product suffices, clear denominators separately in each row. Its product of heights bounds the sum of the absolute values of the resulting integer entries, including the right-hand side. At a vertex, Cramer’s rule has a nonzero integer denominator; Hadamard’s inequality bounds each numerator by the product of the selected row bounds. Convexity extends the estimate to the whole polytope.
-- source:
--   Explicit coarse Cramer–Hadamard bound for the geometric step of Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, https://arxiv.org/abs/2609.31328, §2, (2.1), p. 6; cf. Schrijver, Theory of Linear and Integer Programming (1986), Theorem 10.3.

import Definitions.Def_IntConeFPT_Instance

open IntConeFPT

theorem IntConeFPT.polytope_height_product {m d k : ℕ}
    (A : Matrix (Fin m) (Fin d) ℚ) (B : Matrix (Fin m) (Fin k) ℚ) (b : Fin m → ℚ) :
    let P : Set ((Fin d → ℝ) × (Fin k → ℝ)) :=
      {p | ∀ i, (∑ j, (A i j : ℝ) * p.1 j) + (∑ j, (B i j : ℝ) * p.2 j) ≤ (b i : ℝ)}
    let H := fun q : ℚ => (q.num.natAbs + 1) * q.den
    Bornology.IsBounded P → ∀ p ∈ P,
      InBox ((∏ i, ∏ j, H (A i j)) * (∏ i, ∏ j, H (B i j)) * (∏ i, H (b i))) p := by sorry
