-- Prove2me | Theorems.Thm_MinVolEllipsoid_eq_7
-- name    : MinVolEllipsoid.eq_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:45:38.788516+00:00
-- url     : https://prove2.me/theorems/f0273e8d-a835-45c1-a142-429982e404f1
-- title:
--   Display (7): the completely positive reformulation of $Z(A,b)$
-- statement:
--   Let $\mathcal P\subseteq\mathbb R^K$ satisfy Assumption 1 (p.1): $\mathcal P$ is compact, convex and full-dimensional (has nonempty interior). Let $\mathcal K=\mathrm{cone}(\{[x;1]:x\in\mathcal P\})\subseteq\mathbb R^{K+1}$ be the cone of display (2). Let $A\in\mathbb S^K_{++}$ be symmetric positive definite and $b\in\mathbb R^K$. Then $Z(A,b)$ is the optimal value of the generalized completely positive program
--
--   $$
--   Z(A,b)=\sup\ \mathrm{tr}(A^2X)+2b^\top Ax+b^\top b
--   \quad\text{s.t.}\quad x\in\mathbb R^K,\ X\in\mathbb S^K,\
--   \begin{bmatrix}X & x\\ x^\top & 1\end{bmatrix}\succeq_{\mathcal C^*(\mathcal K)}0.\qquad(7)
--   $$
--
--   The nonconvex maximization of a convex quadratic over $\mathcal P$ is thereby an optimization of a linear function over a convex cone, which admits the copositive dual (8).
--
--   **Formalization Note** "$Z(A,b)=\sup\dots$" is stated as `IsLUB` of the set of objective values of feasible points, which also forces the feasible set to be nonempty. $A^2$ is `A * A`, $\mathrm{tr}$ is `Matrix.trace`.
--
--   Differences from the source:
--
--   - encoding: Z(A, b) = sup of the objective of (7) over its feasible set → IsLUB {objective values of feasible (x, X)} (Zval P A b); reason: IsLUB is the meaning of sup = Z in ℝ and excludes the junk value of sSup on an empty set
--   - encoding: 𝒞*(𝒦): sums of I ≥ 1 terms xᵢxᵢ⊤ → sums of m ≥ 0 terms; reason: 0 ∈ 𝒦, so a zero summand can always be added; same set
--   - encoding: ‖Ax + b‖² with the Euclidean norm → (A *ᵥ x + b) ⬝ᵥ (A *ᵥ x + b) inside MinVolEllipsoid.Zval; reason: the pi type carries the sup norm; the dot product is the squared Euclidean norm
--   - encoding: vectors [x; τ] ∈ ℝ^{K+1} with τ the last coordinate → Sum.elim x (fun _ => τ) : Fin n ⊕ Unit → ℝ, τ at the Unit coordinate; reason: Lean convention for ℝ^{K+1}; same vectors
--   - encoding: 𝒫 full-dimensional (Assumption 1) → (interior P).Nonempty; reason: the paper's own reading in the proof of Lemma 2, p.7 ("Since 𝒫 has nonempty interior")
--   - encoding: 𝒦 = cone({[x; 1] : x ∈ 𝒫}), the conic hull → liftCone P, the finite nonnegative combinations of the lifted points (including 0); reason: the conic hull of a set is the set of its finite nonnegative combinations
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, proof of Theorem 1, display (7), p.8

import Mathlib
import Definitions.Def_MinVolEllipsoid_Zval
import Definitions.Def_MinVolEllipsoid_liftCone
import Definitions.Def_MinVolEllipsoid_GenCompletelyPositive
import Definitions.Def_MinVolEllipsoid_borderedMatrix

open Matrix

namespace MinVolEllipsoid

/-- **The completely positive reformulation (7)** (Mittal & Hanasusanto, arXiv:1807.07507v4,
proof of Theorem 1, display (7), p.8):

`Z(A, b) = sup tr(A²X) + 2b⊤Ax + b⊤b  s.t.  x ∈ ℝᴷ, X ∈ 𝕊ᴷ, [X x; x⊤ 1] ⪰_{𝒞*(𝒦)} 0`.

For `P ⊆ ℝᴷ` satisfying Assumption 1 (p.1), `𝒦 = liftCone P` as in (2), `A ∈ 𝕊ᴷ₊₊` and
`b ∈ ℝᴷ`, `Z(A, b)` is the least upper bound of the objective values of (7) over its feasible set.

**Formalization Note** "sup = Z" is `IsLUB`, which also forces the feasible set to be nonempty, so
no junk value of `sSup` can satisfy it. `A²` is `A * A`, `tr` is `Matrix.trace`, `b⊤Ax` is
`b ⬝ᵥ (A *ᵥ x)`, and `[X x; x⊤ 1]` is `borderedMatrix X x x 1`. -/
theorem eq_7 {n : ℕ} (P : Set (Fin n → ℝ)) (hPc : IsCompact P) (hPcv : Convex ℝ P)
    (hPi : (interior P).Nonempty) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) :
    IsLUB {z : ℝ | ∃ (x : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℝ), X.IsSymm ∧
        GenCompletelyPositive (liftCone P) (borderedMatrix X x x 1) ∧
        z = trace (A * A * X) + 2 * (b ⬝ᵥ (A *ᵥ x)) + b ⬝ᵥ b}
      (Zval P A b) := by sorry

end MinVolEllipsoid
