-- Prove2me | Theorems.Thm_MinVolEllipsoid_eq_8
-- name    : MinVolEllipsoid.eq_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:45:58.59899+00:00
-- url     : https://prove2.me/theorems/0897cf3b-a538-4128-9861-e95cb30191b1
-- title:
--   Display (8): $Z(A,b)=Z_d(A,b)$ and the copositive dual attains it
-- statement:
--   Let $\mathcal P\subseteq\mathbb R^K$ satisfy Assumption 1 (p.1): $\mathcal P$ is compact, convex and full-dimensional (has nonempty interior). Let $\mathcal K=\mathrm{cone}(\{[x;1]:x\in\mathcal P\})\subseteq\mathbb R^{K+1}$ be the cone of display (2). Let $A\in\mathbb S^K_{++}$ be symmetric positive definite and $b\in\mathbb R^K$. Let
--
--   $$
--   Z_d(A,b)=\inf_{\rho\in\mathbb R}\ \rho\quad\text{s.t.}\quad
--   \begin{bmatrix}-A^2 & -Ab\\ -b^\top A & \rho-b^\top b\end{bmatrix}\succeq_{\mathcal C(\mathcal K)}0.\qquad(8)
--   $$
--
--   Then strong duality holds, $Z(A,b)=Z_d(A,b)$, and the infimum is attained: $\rho=Z(A,b)$ is feasible for (8) and every feasible $\rho$ satisfies $\rho\ge Z(A,b)$.
--
--   This is the step that converts the semi-infinite constraint $Z(A,b)\le1$ into a single copositive constraint.
--
--   **Formalization Note** The two claims "$Z=Z_d$" and "there exists a dual feasible solution which attains the value $Z(A,b)$" are encoded together as `IsLeast` of the feasible set of (8) at `Zval P A b`. The row $-b^\top A$ is written as the vector–matrix product, exactly as printed.
--
--   Differences from the source:
--
--   - encoding: Z(A, b) = Z_d(A, b) and the dual infimum is attained → IsLeast {ρ | (8) holds} (Zval P A b); reason: IsLeast is exactly 'the infimum equals Z and is attained'
--   - encoding: ‖Ax + b‖² with the Euclidean norm → (A *ᵥ x + b) ⬝ᵥ (A *ᵥ x + b) inside MinVolEllipsoid.Zval; reason: the pi type carries the sup norm; the dot product is the squared Euclidean norm
--   - encoding: vectors [x; τ] ∈ ℝ^{K+1} with τ the last coordinate → Sum.elim x (fun _ => τ) : Fin n ⊕ Unit → ℝ, τ at the Unit coordinate; reason: Lean convention for ℝ^{K+1}; same vectors
--   - encoding: 𝒫 full-dimensional (Assumption 1) → (interior P).Nonempty; reason: the paper's own reading in the proof of Lemma 2, p.7 ("Since 𝒫 has nonempty interior")
--   - encoding: 𝒦 = cone({[x; 1] : x ∈ 𝒫}), the conic hull → liftCone P, the finite nonnegative combinations of the lifted points (including 0); reason: the conic hull of a set is the set of its finite nonnegative combinations
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, proof of Theorem 1, display (8) and the paragraph after it, p.8

import Mathlib
import Definitions.Def_MinVolEllipsoid_Zval
import Definitions.Def_MinVolEllipsoid_liftCone
import Definitions.Def_MinVolEllipsoid_GenCopositive
import Definitions.Def_MinVolEllipsoid_borderedMatrix

open Matrix

namespace MinVolEllipsoid

/-- **Strong duality for (7)–(8), with dual attainment** (Mittal & Hanasusanto,
arXiv:1807.07507v4, proof of Theorem 1, display (8) and the paragraph after it, p.8):

`Z_d(A, b) = inf_{ρ∈ℝ} ρ  s.t.  [−A² −Ab; −b⊤A ρ − b⊤b] ⪰_{𝒞(𝒦)} 0`,

"strong duality holds and Z(A, b) = Z_d(A, b). Furthermore, there exists a dual feasible solution
which attains the value Z(A, b)".

For `P ⊆ ℝᴷ` satisfying Assumption 1 (p.1), `𝒦 = liftCone P` as in (2), `A ∈ 𝕊ᴷ₊₊` and
`b ∈ ℝᴷ`, `Z(A, b)` is the least element of the feasible set of (8): it is feasible (attainment)
and it is a lower bound of every feasible `ρ` (so `Z_d = Z`).

**Formalization Note** `IsLeast` encodes both `Z_d = Z` and attainment. The dual matrix is
`borderedMatrix (-(A * A)) (-(A *ᵥ b)) (-(b ᵥ* A)) (ρ - b ⬝ᵥ b)`, with the row `−b⊤A` written as
the vector–matrix product `b ᵥ* A`, exactly as printed. -/
theorem eq_8 {n : ℕ} (P : Set (Fin n → ℝ)) (hPc : IsCompact P) (hPcv : Convex ℝ P)
    (hPi : (interior P).Nonempty) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) :
    IsLeast {ρ : ℝ | GenCopositive (liftCone P)
        (borderedMatrix (-(A * A)) (-(A *ᵥ b)) (-(b ᵥ* A)) (ρ - b ⬝ᵥ b))}
      (Zval P A b) := by sorry

end MinVolEllipsoid
