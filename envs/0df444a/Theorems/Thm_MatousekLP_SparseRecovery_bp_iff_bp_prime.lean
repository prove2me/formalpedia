-- Prove2me | Theorems.Thm_MatousekLP_SparseRecovery_bp_iff_bp_prime
-- name    : MatousekLP.SparseRecovery.bp_iff_bp_prime
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T13:38:58.881801+00:00
-- url     : https://prove2.me/theorems/1e58d067-f94d-474b-b5f9-8f7f5943daca
-- title:
--   §8.5, p. 170 — basis pursuit (BP) is the linear program (BP′)
-- statement:
--   Let $A$ be a real $m\times n$ matrix and $b\in\mathbb{R}^m$. Consider basis pursuit
--   $$\text{(BP)}\quad\min\ \|x\|_1\ \text{ s.t. } Ax=b,\qquad\qquad \text{(BP}'\text{)}\quad\min\ u_1+\dots+u_n\ \text{ s.t. } Ax=b,\ -u\le x\le u,\ u\ge 0 .$$
--   Then:
--
--   1. in every optimal solution $(x,u)$ of (BP′), $u_i=|x_i|$ for every $i$;
--   2. $x$ is an optimal solution of (BP) if and only if $(x,|x|)$ is an optimal solution of (BP′), where $|x|=(|x_1|,\dots,|x_n|)$.
--
--   This is what makes basis pursuit solvable by linear programming.
--
--   **Formalization Note** The book's sentence ("in an optimal solution of (BP′) we have $u_i=|x_i|$ for every $i$") is part 1; the equivalence of the two problems that the book draws from it is formalized as part 2. Optimality is stated against every feasible point.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 170, §8.5 (equivalence of (BP) and (BP′), unnumbered)

import Mathlib
import Definitions.Def_MatousekLP_SparseRecovery_BasisPursuit

namespace MatousekLP.SparseRecovery

open Matrix

/-- **Equivalence of (BP) and (BP′)**, §8.5, p. 170, Matoušek & Gärtner, *Understanding and
Using Linear Programming*, Springer 2007: "in an optimal solution of (BP′) we have `uᵢ = |xᵢ|`
for every `i`".  Formalized as: (1) every optimal solution `(x, u)` of (BP′) has `uᵢ = |xᵢ|`
for all `i`; (2) `x` is an optimal solution of (BP) if and only if `(x, |x|)` is an optimal
solution of (BP′), where `|x|` is the componentwise absolute value. -/
theorem bp_iff_bp_prime {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (∀ x u : Fin n → ℝ, IsBPPrimeOptimal A b x u → ∀ i, u i = |x i|) ∧
      (∀ x : Fin n → ℝ, IsBPOptimal A b x ↔ IsBPPrimeOptimal A b x (fun i => |x i|)) := by sorry

end MatousekLP.SparseRecovery
