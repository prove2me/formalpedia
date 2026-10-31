-- Prove2me | Theorems.Thm_MinVolEllipsoid_eq_9
-- name    : MinVolEllipsoid.eq_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:46:16.241493+00:00
-- url     : https://prove2.me/theorems/a780d631-d1c3-4e09-a11b-106a08928880
-- title:
--   Display (9): $Z(A,b)\le1$ iff $[0\ 0;\ 0\ 1]\succeq_{\mathcal C(\mathcal K)}[A\ b]^\top[A\ b]$
-- statement:
--   Let $\mathcal P\subseteq\mathbb R^K$ satisfy Assumption 1 (p.1): $\mathcal P$ is compact, convex and full-dimensional (has nonempty interior). Let $\mathcal K=\mathrm{cone}(\{[x;1]:x\in\mathcal P\})\subseteq\mathbb R^{K+1}$ be the cone of display (2). Let $A\in\mathbb S^K_{++}$ be symmetric positive definite and $b\in\mathbb R^K$. Then
--
--   $$
--   Z(A,b)\le1\quad\Longleftrightarrow\quad
--   \begin{bmatrix}0 & 0\\ 0 & 1\end{bmatrix}\succeq_{\mathcal C(\mathcal K)}\begin{bmatrix}A & b\end{bmatrix}^\top\begin{bmatrix}A & b\end{bmatrix},\qquad(9)
--   $$
--
--   where both sides are $(K+1)\times(K+1)$ matrices and $[A\ b]$ is the $K\times(K+1)$ matrix with the column $b$ appended to $A$.
--
--   Condition (9) is a single copositive constraint, but it is quadratic in $(A,b)$; Lemma 5 then linearizes it into (3).
--
--   Differences from the source:
--
--   - encoding: ‖Ax + b‖² with the Euclidean norm → (A *ᵥ x + b) ⬝ᵥ (A *ᵥ x + b) inside MinVolEllipsoid.Zval; reason: the pi type carries the sup norm; the dot product is the squared Euclidean norm
--   - encoding: vectors [x; τ] ∈ ℝ^{K+1} with τ the last coordinate → Sum.elim x (fun _ => τ) : Fin n ⊕ Unit → ℝ, τ at the Unit coordinate; reason: Lean convention for ℝ^{K+1}; same vectors
--   - encoding: 𝒫 full-dimensional (Assumption 1) → (interior P).Nonempty; reason: the paper's own reading in the proof of Lemma 2, p.7 ("Since 𝒫 has nonempty interior")
--   - encoding: 𝒦 = cone({[x; 1] : x ∈ 𝒫}), the conic hull → liftCone P, the finite nonnegative combinations of the lifted points (including 0); reason: the conic hull of a set is the set of its finite nonnegative combinations
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, proof of Theorem 1, display (9), p.8

import Mathlib
import Definitions.Def_MinVolEllipsoid_Zval
import Definitions.Def_MinVolEllipsoid_liftCone
import Definitions.Def_MinVolEllipsoid_GenCopositive
import Definitions.Def_MinVolEllipsoid_borderedMatrix
import Definitions.Def_MinVolEllipsoid_stackAb

open Matrix

namespace MinVolEllipsoid

/-- **`Z(A, b) ≤ 1` iff (9)** (Mittal & Hanasusanto, arXiv:1807.07507v4, proof of Theorem 1,
display (9), p.8): `Z(A, b) ≤ 1` if and only if

`[0 0; 0 1] ⪰_{𝒞(𝒦)} [A b]⊤ [A b]`.

For `P ⊆ ℝᴷ` satisfying Assumption 1 (p.1), `𝒦 = liftCone P` as in (2), `A ∈ 𝕊ᴷ₊₊` and
`b ∈ ℝᴷ`.

**Formalization Note** `[0 0; 0 1]` is `borderedMatrix 0 0 0 1` and `[A b]` is the `K × (K+1)`
matrix `stackAb A b`; both sides are `(K+1) × (K+1)` over `Fin n ⊕ Unit`. -/
theorem eq_9 {n : ℕ} (P : Set (Fin n → ℝ)) (hPc : IsCompact P) (hPcv : Convex ℝ P)
    (hPi : (interior P).Nonempty) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) :
    Zval P A b ≤ 1 ↔
      GenCopositive (liftCone P)
        (borderedMatrix 0 0 0 1 - (stackAb A b)ᵀ * stackAb A b) := by sorry

end MinVolEllipsoid
