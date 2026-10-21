-- Prove2me | Theorems.Thm_ModernConvex_Ellipsoids_sum_containment_sdp
-- name    : ModernConvex.Ellipsoids.sum_containment_sdp
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:34:59.176694+00:00
-- url     : https://prove2.me/theorems/27b58991-97ad-4f1f-87f2-25a6afa8e119
-- title:
--   (D) — if the SDP max{Tr(M[Z]X) | Tr(BⁱX) ≤ 1, X ⪰ 0} has value ≤ 1, then W[Z] ⊇ W₁ + ⋯ + W_m
-- statement:
--   Let $B_1,\dots,B_m$ be positive definite $n\times n$ matrices and $W_i=\{x \mid x^TB_ix\le1\}$ the corresponding ellipsoids centred at the origin. Let $B^i$ be the $(mn)\times(mn)$ block-diagonal matrix whose only nonzero diagonal block (the $i$-th) is $B_i$, and $M[Z]$ the $(mn)\times(mn)$ matrix of $m^2$ blocks all equal to $Z$.
--
--   Let $Z$ be a positive definite $n\times n$ matrix such that the optimal value of the semidefinite program
--   $$\max_X\Big\{\operatorname{Tr}(M[Z]X) \;\Big|\; \operatorname{Tr}(B^iX)\le1,\ i=1,\dots,m,\ X\succeq0\Big\}\qquad\text{(SDP)}$$
--   is at most $1$. Then the ellipsoid $W[Z]=\{x \mid x^TZx\le1\}$ contains the arithmetic sum $W_1+\dots+W_m$.
--
--   This is the semidefinite relaxation that makes the outer approximation of a sum of ellipsoids tractable.
--
--   **Formalization Note** "The optimal value of (SDP) is $\le1$" is stated as: every feasible $X$, i.e. every symmetric positive semidefinite $(mn)\times(mn)$ matrix with $\operatorname{Tr}(B^iX)\le1$ for all $i$, has $\operatorname{Tr}(M[Z]X)\le1$. This avoids a supremum. The standing assumption $B_i\succ0$ of Problem (O) (p. 265) is a hypothesis. The $(mn)$ coordinates are indexed by `Fin m × Fin n`.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 267, statement (D)

import Mathlib
import Definitions.Def_ModernConvex_Ellipsoids_Ellipsoid
import Definitions.Def_ModernConvex_Ellipsoids_Programs

open Matrix

namespace ModernConvex.Ellipsoids

/-- Ben-Tal–Nemirovski, statement (D), p. 267 (setting of Problem (O), p. 265:
`Wᵢ = {x | xᵀBᵢx ≤ 1}`, `Bᵢ ≻ 0`). Let a positive definite `n × n` matrix `Z` be such that the
optimal value of the semidefinite program
`max_X { Tr(M[Z]X) | Tr(BⁱX) ≤ 1, i = 1, …, m, X ⪰ 0 }`   (SDP)
is `≤ 1`, i.e. every feasible `X` has `Tr(M[Z]X) ≤ 1`. Then the ellipsoid `W[Z] = {x | xᵀZx ≤ 1}`
contains the arithmetic sum `W₁ + ⋯ + W_m`. -/
theorem sum_containment_sdp {m n : ℕ} (B : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ i, (B i).PosDef) (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : Z.PosDef)
    (hval : ∀ X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℝ, DFeasible B X →
      (blockAll Z * X).trace ≤ 1) :
    minkowskiSum (fun i => quadSet (B i)) ⊆ quadSet Z := by sorry

end ModernConvex.Ellipsoids
