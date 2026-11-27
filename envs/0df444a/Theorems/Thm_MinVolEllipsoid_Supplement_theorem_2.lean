-- Prove2me | Theorems.Thm_MinVolEllipsoid_Supplement_theorem_2
-- name    : MinVolEllipsoid.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:33:40.91135+00:00
-- url     : https://prove2.me/theorems/ad707032-2c8e-5175-9819-92f0aa5b8659
-- title:
--   Theorem 2 — an SDP certificate (11) implies that $\mathcal E(A,b)$ contains the polytope $\{Sx\le t\}$
-- statement:
--   Let $\mathcal P=\{x\in\mathbb R^K: Sx\le t\}$ with $S\in\mathbb R^{J\times K}$, $t\in\mathbb R^J$ be a polytope satisfying Assumption 1, i.e. compact, convex and with nonempty interior. Let $A\in\mathbb S^K_{++}$ be positive definite and $b\in\mathbb R^K$, and write $\mathcal E(A,b)=\{x\in\mathbb R^K:\|Ax+b\|^2\le1\}$.
--
--   If there exist $N\in\mathbb R^{J\times J}_+$ (entrywise nonnegative), $F\in\mathbb S^K$, $g\in\mathbb R^K$ and $h\in\mathbb R$ such that
--
--   $$
--   \begin{bmatrix}F & g\\ g^\top & h-1\end{bmatrix}\preceq-\begin{bmatrix}-S^\top\\ t^\top\end{bmatrix}N\begin{bmatrix}-S & t\end{bmatrix}
--   \quad\text{and}\quad
--   \begin{bmatrix}F & g & A\\ g^\top & h & b^\top\\ A & b & \mathbb I\end{bmatrix}\succeq0, \tag{11}
--   $$
--
--   then $\mathcal P\subseteq\mathcal E(A,b)$.
--
--   The theorem replaces the generalized copositive constraint of Theorem 1 by a semidefinite one, which yields the tractable SDP (12) whose optimal ellipsoid $\mathcal E_{\mathrm{sdp}}$ contains $\mathcal P$. Only this direction holds in general.
--
--   **Formalization Note** The dimension $K$ is $n$ and $[J]$ is `Fin m`. $P\preceq Q$ is the order of p.5, $Q-P\in\mathbb S_+$, written with Mathlib's `PosSemidef` (which includes symmetry). The conditions (11) are bundled in `MinVolEllipsoid.Supplement.Cond11`; the ellipsoid is the published `ConvexOptimization.ellipsoidBody`.
--
--   Differences from the source:
--   - reading: ⪯ between [F g; g⊤ h − 1] and −[−S⊤; t⊤]N[−S t] with N not required symmetric → (−𝒮⊤N𝒮 − [F g; g⊤ h − 1]).PosSemidef, i.e. the difference is symmetric positive semidefinite; reason: p.5 defines P ⪰ Q only for P, Q ∈ 𝕊ᴷ, as P − Q ∈ 𝕊₊ᴷ, so the literal reading requires the right-hand side to be symmetric when N is not.
--   - encoding: ℝᴷ, ℝᴶ, ‖Ax + b‖² → `Fin n → ℝ`, `Fin m → ℝ`, dot product; reason: Lean convention, same instances.
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, Theorem 2, display (11), p.10

import Mathlib
import Definitions.Def_ConvexOptimization_ellipsoidBody
import Definitions.Def_MinVolEllipsoid_Supplement_polytope
import Definitions.Def_MinVolEllipsoid_Supplement_Cond11

namespace MinVolEllipsoid.Supplement

/-- **Theorem 2** (Mittal & Hanasusanto, *Finding Minimum Volume Circumscribing Ellipsoids Using
Generalized Copositive Programming*, arXiv:1807.07507v4, Theorem 2, display (11), p.10).

Let `𝒫 = {x ∈ ℝᴷ : Sx ≤ t}` (10) be a polytope that satisfies Assumption 1 (compact, convex,
full-dimensional, p.1). Consider any `A ∈ 𝕊ᴷ₊₊` and `b ∈ ℝᴷ`. Then the ellipsoid `ℰ(A, b)` contains
`𝒫` if there exist `N ∈ ℝ^{J×J}_+`, `F ∈ 𝕊ᴷ`, `g ∈ ℝᴷ`, `h ∈ ℝ` such that

`[F g; g⊤ h − 1] ⪯ −[−S⊤; t⊤] N [−S t]`   and   `[F g A; g⊤ h b⊤; A b 𝕀] ⪰ 0`.   (11)

**Formalization Note** The dimension is `n` (the paper's `K`) and `J` is `Fin m`. "Full-dimensional"
is `(interior P).Nonempty`. `ℰ(A, b)` is the published `ConvexOptimization.ellipsoidBody A b`;
`A ∈ 𝕊ᴷ₊₊` is `A.PosDef`. The conditions (11), with `N ≥ 0` entrywise and `F ∈ 𝕊ᴷ`, are
`Cond11 S t A b N F g h`. The implication is one-directional, as printed. -/
theorem theorem_2 {n m : ℕ} (S : Matrix (Fin m) (Fin n) ℝ) (t : Fin m → ℝ)
    (hPc : IsCompact (polytope S t)) (hPcv : Convex ℝ (polytope S t))
    (hPi : (interior (polytope S t)).Nonempty)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (b : Fin n → ℝ)
    (hcert : ∃ (N : Matrix (Fin m) (Fin m) ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → ℝ)
      (h : ℝ), Cond11 S t A b N F g h) :
    polytope S t ⊆ ConvexOptimization.ellipsoidBody A b := by sorry

end MinVolEllipsoid.Supplement
