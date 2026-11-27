-- Prove2me | Theorems.Thm_MinVolEllipsoid_Supplement_theorem_4
-- name    : MinVolEllipsoid.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:35:44.139955+00:00
-- url     : https://prove2.me/theorems/153654c9-8bc5-564e-a26f-594feb2084a5
-- title:
--   Theorem 4 — an SDP certificate (17) implies that $\mathcal E(A,b)$ contains the set (16)
-- statement:
--   Let $\mathcal P=\{x\in\mathbb R^K:\ Sx\le t,\ \|Q_ix+q_i\|^2\le1\ \forall i\in[I]\}$ with $S\in\mathbb R^{J\times K}$, $t\in\mathbb R^J$, $Q_i\in\mathbb S^K$ and $q_i\in\mathbb R^K$. Let $A\in\mathbb S^K_{++}$ and $b\in\mathbb R^K$. If there exist $N\in\mathbb R^{J\times J}_+$, $F\in\mathbb S^K$, $g\in\mathbb R^K$, $h\in\mathbb R$, $\lambda_i\ge0$ $(i\in[I])$, $\alpha_{ij}\in\mathbb R^K$ and $\kappa_{ij}\in\mathbb R$ $(i\in[I],j\in[J])$ such that
--
--   $$
--   \begin{aligned}
--   &\|\alpha_{ij}\|\le\kappa_{ij}\quad\forall i\in[I]\ \forall j\in[J],\\
--   &\begin{bmatrix}F & g\\ g^\top & h-1\end{bmatrix}\preceq-\mathcal S^\top N\mathcal S+\sum_{i\in[I]}\lambda_iJ_i-\sum_{i\in[I],j\in[J]}M_{ij}(\alpha_{ij},\kappa_{ij}),\\
--   &\begin{bmatrix}F & g & A\\ g^\top & h & b^\top\\ A & b & \mathbb I\end{bmatrix}\succeq0,
--   \end{aligned}\tag{17}
--   $$
--
--   where $\mathcal S=[-S\ \ t]$, $J_i=\begin{bmatrix}Q_i^2 & Q_i^\top q_i\\ q_i^\top Q_i & q_i^\top q_i-1\end{bmatrix}$ and $M_{ij}(\alpha,\kappa)$ is the matrix defined on p.15, then $\mathcal E(A,b)=\{x:\|Ax+b\|^2\le1\}$ contains $\mathcal P$.
--
--   The certificate yields the SDP restriction (18) of the minimum volume ellipsoid problem for sets cut out by affine and ellipsoidal constraints, generalizing Theorem 2.
--
--   **Formalization Note** $[I]$ is `Fin p` (possibly empty), $[J]$ is `Fin m`, the dimension is $n$, and $\lambda$ is written `lam`. $\|\alpha\|=\sqrt{\alpha^\top\alpha}$ is the Euclidean norm. $P\preceq Q$ is `(Q - P).PosSemidef`. $\mathcal S$, $J_i$, $M_{ij}$ are `calS`, `Jmat`, `Mmat` of this supplement. As on the page, Assumption 1 is not assumed.
--
--   Differences from the source:
--   - reading: ⪯ in (17) between [F g; g⊤ h − 1] and a right-hand side containing −𝒮⊤N𝒮 with N not required symmetric → the difference is symmetric PSD (`PosSemidef`); reason: p.5 defines ⪰ only on 𝕊ᴷ⁺¹, as membership of the difference in 𝕊₊.
--   - encoding: index sets [I], [J], Euclidean norm, λ_i → `Fin p`, `Fin m`, √(α ⬝ᵥ α), `lam i`; reason: Lean convention, same instances.
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, Theorem 4, displays (16)–(17), p.15

import Mathlib
import Definitions.Def_ConvexOptimization_ellipsoidBody
import Definitions.Def_MinVolEllipsoid_borderedMatrix
import Definitions.Def_MinVolEllipsoid_ineq3Right
import Definitions.Def_MinVolEllipsoid_Supplement_calS
import Definitions.Def_MinVolEllipsoid_Supplement_quadSet
import Definitions.Def_MinVolEllipsoid_Supplement_Jmat
import Definitions.Def_MinVolEllipsoid_Supplement_Mmat

open Matrix

namespace MinVolEllipsoid.Supplement

/-- **Theorem 4** (Mittal & Hanasusanto, arXiv:1807.07507v4, Theorem 4, displays (16)–(17), p.15).

Let `𝒫 = {x ∈ ℝᴷ : Sx ≤ t, ‖Q_i x + q_i‖² ≤ 1 ∀ i ∈ [I]}` (16) with `S ∈ ℝ^{J×K}`, `t ∈ ℝᴶ`,
`Q_i ∈ 𝕊ᴷ`, `q_i ∈ ℝᴷ`. Consider any `A ∈ 𝕊ᴷ₊₊` and `b ∈ ℝᴷ`. Then the ellipsoid `ℰ(A, b)` contains
`𝒫` if there exist `N ∈ ℝ^{J×J}_+`, `F ∈ 𝕊ᴷ`, `g ∈ ℝᴷ`, `h ∈ ℝ`, `λ_i ≥ 0`, `α_ij ∈ ℝᴷ`,
`κ_ij ∈ ℝ` such that

`‖α_ij‖ ≤ κ_ij ∀ i, j`,
`[F g; g⊤ h − 1] ⪯ −𝒮⊤N𝒮 + ∑_{i∈[I]} λ_i J_i − ∑_{i∈[I], j∈[J]} M_ij(α_ij, κ_ij)`,
`[F g A; g⊤ h b⊤; A b 𝕀] ⪰ 0`,   (17)

with `𝒮 = [−S t]`, `J_i` and `M_ij(α, κ)` as on p.15.

**Formalization Note** `I` is `Fin p` (possibly empty), `J` is `Fin m`, the dimension is `n`.
`λ` is written `lam`. `‖α‖` is the Euclidean norm `√(α ⬝ᵥ α)`. `P ⪯ Q` is `(Q - P).PosSemidef`
(p.5; Mathlib's `PosSemidef` includes symmetry). `𝒮` is `calS S t`, `J_i` is `Jmat (Q i) (q i)`,
`M_ij(α, κ)` is `Mmat (S j) (t j) (Q i) (q i) α κ`. Assumption 1 is not stated, as on the page. -/
theorem theorem_4 {n m p : ℕ} (S : Matrix (Fin m) (Fin n) ℝ) (t : Fin m → ℝ)
    (Q : Fin p → Matrix (Fin n) (Fin n) ℝ) (hQ : ∀ i, (Q i).IsSymm) (q : Fin p → Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (b : Fin n → ℝ)
    (hcert : ∃ (N : Matrix (Fin m) (Fin m) ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → ℝ)
      (h : ℝ) (lam : Fin p → ℝ) (α : Fin p → Fin m → Fin n → ℝ) (κ : Fin p → Fin m → ℝ),
      (∀ j j', 0 ≤ N j j') ∧ F.IsSymm ∧ (∀ i, 0 ≤ lam i) ∧
      (∀ i j, Real.sqrt (α i j ⬝ᵥ α i j) ≤ κ i j) ∧
      ((-((calS S t)ᵀ * N * calS S t) + ∑ i, lam i • Jmat (Q i) (q i) -
          ∑ i, ∑ j, Mmat (S j) (t j) (Q i) (q i) (α i j) (κ i j)) -
        MinVolEllipsoid.borderedMatrix F g g (h - 1)).PosSemidef ∧
      (MinVolEllipsoid.ineq3Right A b F g h).PosSemidef) :
    quadSet S t Q q ⊆ ConvexOptimization.ellipsoidBody A b := by sorry

end MinVolEllipsoid.Supplement
