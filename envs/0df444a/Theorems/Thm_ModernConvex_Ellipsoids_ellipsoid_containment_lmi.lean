-- Prove2me | Theorems.Thm_ModernConvex_Ellipsoids_ellipsoid_containment_lmi
-- name    : ModernConvex.Ellipsoids.ellipsoid_containment_lmi
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:34:52.504879+00:00
-- url     : https://prove2.me/theorems/220fdd9e-23d8-4dac-b988-012caa0c6fe4
-- title:
--   Proposition 4.9.3 — E(Z, z) ⊂ W(Y, y) iff an LMI in one scalar λ is solvable
-- statement:
--   Let $q\ge1$, $Z\in\mathbb R^{n\times q}$, $z\in\mathbb R^n$, and let $E(Z,z)=\{x=Zu+z \mid u^Tu\le1\}$ be an ellipsoid, possibly flat. Let $Y\in\mathbb R^{n\times n}$ with $\operatorname{Det}Y\ne0$, $y\in\mathbb R^n$, and let $W(Y,y)=\{x \mid (x-y)^TY^TY(x-y)\le1\}$ be the corresponding full-dimensional ellipsoid. Then $E(Z,z)\subseteq W(Y,y)$ if and only if there is $\lambda\in\mathbb R$ with
--   $$\begin{pmatrix} I_n & Y(z-y) & YZ\\ (z-y)^TY^T & 1-\lambda & 0\\ Z^TY^T & 0 & \lambda I_q\end{pmatrix}\succeq0 \qquad(4.9.111)$$
--   and also if and only if there is $\lambda\in\mathbb R$ with
--   $$\begin{pmatrix} Y^{-1}(Y^{-1})^T & z-y & Z\\ (z-y)^T & 1-\lambda & 0\\ Z^T & 0 & \lambda I_q\end{pmatrix}\succeq0. \qquad(4.9.112)$$
--
--   The proposition turns containment of one ellipsoid in another into a linear matrix inequality. This is what makes inner approximation of intersections of ellipsoids, and outer approximation of their unions, explicit semidefinite programs.
--
--   **Formalization Note** $\succeq0$ is Mathlib's `PosSemidef` (symmetric positive semidefinite). The matrices are indexed by `(Fin n ⊕ Unit) ⊕ Fin q`, with the middle scalar entry in the `Unit` slot. Blank entries of the book's displays are zero blocks. $\lambda$ ranges over all reals, as in the book; nonnegativity is a consequence. The ellipsoid is the image of the unit ball of some $\mathbb R^q$ with $q\ge1$: the book's proof uses that the block $\lambda I_q$ forces $\lambda\ge0$, and for $q=0$ both matrix inequalities would be solvable with a very negative $\lambda$ whatever $z$ is.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 262, Proposition 4.9.3

import Mathlib
import Definitions.Def_ModernConvex_Ellipsoids_Ellipsoid
import Definitions.Def_ModernConvex_Ellipsoids_Programs

open Matrix

namespace ModernConvex.Ellipsoids

/-- Ben-Tal–Nemirovski, Proposition 4.9.3, p. 262. An ellipsoid
`E(Z, z) = {x = Zu + z | uᵀu ≤ 1}` (`Z ∈ M^{n,q}`) is contained in the full-dimensional ellipsoid
`W(Y, y) = {x | (x − y)ᵀYᵀY(x − y) ≤ 1}` (`Y ∈ M^{n,n}`, `Det Y ≠ 0`) if and only if there exists
`λ` with
`( Iₙ, Y(z − y), YZ ; (z − y)ᵀYᵀ, 1 − λ, 0 ; ZᵀYᵀ, 0, λI_q ) ⪰ 0`   (4.9.111),
as well as if and only if there exists `λ` with
`( Y⁻¹(Y⁻¹)ᵀ, z − y, Z ; (z − y)ᵀ, 1 − λ, 0 ; Zᵀ, 0, λI_q ) ⪰ 0`   (4.9.112).
The ellipsoid is the image of the unit ball of some `ℝ^q` with `q ≥ 1` (the proof's "P(λ) can be
positive semidefinite only when λ ≥ 0" needs the block `λI_q` to be nonempty; at `q = 0` both LMIs
are solvable with `λ ≪ 0` whatever `z`). -/
theorem ellipsoid_containment_lmi {n q : ℕ} (Z : Matrix (Fin n) (Fin q) ℝ) (z : Fin n → ℝ)
    (Y : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) (hY : Y.det ≠ 0) (hq : 0 < q) :
    (ellipsoid Z z ⊆ quadEllipsoid Y y ↔
      ∃ lam : ℝ, (block3 1 (Y *ᵥ (z - y)) (Y * Z) (1 - lam) (lam • 1)).PosSemidef) ∧
    (ellipsoid Z z ⊆ quadEllipsoid Y y ↔
      ∃ lam : ℝ, (block3 (Y⁻¹ * (Y⁻¹)ᵀ) (z - y) Z (1 - lam) (lam • 1)).PosSemidef) := by sorry

end ModernConvex.Ellipsoids
