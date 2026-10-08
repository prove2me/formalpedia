-- Prove2me | Theorems.Thm_IRLSM_RIP_block_decomposition
-- name    : IRLSM.RIP.block_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:44:01.438403+00:00
-- url     : https://prove2.me/theorems/2443fd92-6aef-4e23-97b4-0d6014734efe
-- title:
--   Proof of Proposition 6.8, p. 19 — the block decomposition X = H₀ + H_c relative to the SVD of X₁
-- statement:
--   Let $X, X_1$ be real $n\times p$ matrices and $k \in \mathbb N$. Let $U \in \mathbb R^{n\times n}$ and $V \in \mathbb R^{p\times p}$ be orthogonal and let $X_1 = U D V^{\top}$, where $D \in \mathbb R^{n\times p}$ vanishes outside its top-left $k\times k$ block (for a singular value decomposition, that block is $\Sigma$). Set $\hat H = U^{\top} X V$, partition it as
--   $$
--   \hat H = \begin{pmatrix} \hat H_{11} & \hat H_{12} \\ \hat H_{21} & \hat H_{22}\end{pmatrix}, \qquad \hat H_{11} \in \mathbb R^{k\times k},
--   $$
--   and put
--   $$
--   H_0 = U \begin{pmatrix} \hat H_{11} & \hat H_{12} \\ \hat H_{21} & 0\end{pmatrix} V^{\top}, \qquad H_c = U \begin{pmatrix} 0 & 0 \\ 0 & \hat H_{22}\end{pmatrix} V^{\top}.
--   $$
--   Then $X = H_0 + H_c$, $\operatorname{rank} H_0 \le 2k$, $X_1 H_c^{\top} = 0$, $X_1^{\top} H_c = 0$ and $\langle H_0, H_c\rangle = 0$.
--
--   This is the decomposition that the proof of Proposition 6.8 produces for the strong rank null space property: $H_0$ and $H_c$ play the roles of $H_1$ and $H_2$ of Definition 6.4.
--
--   **Formalization Note.** Indices are 0-based, so the top-left block is $\{i < k,\ j < k\}$. The top-left block of $D$ may be any $k\times k$ matrix, not only a diagonal $\Sigma$; this is stronger than the page, whose argument does not use diagonality. The page's assumption $X \in \ker\mathcal S$ is not used by this step and is omitted (also stronger).
-- source:
--   Fornasier, Rauhut, Ward, Low-rank matrix recovery via iteratively reweighted least squares minimization, arXiv:1010.2471v4 (2011), proof of Proposition 6.8, p. 19, first paragraph (definition of Ĥ, H0, Hc)

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic

open HighDimStat.MatrixRank Matrix

namespace IRLSM.RIP

/-- The block decomposition in the proof of Proposition 6.8: let `X₁ = U (Σ 0; 0 0) Vᵀ` with
`U`, `V` orthogonal and `Σ` the top-left `k × k` block, put `Ĥ = Uᵀ X V`, and let `H₀`
(resp. `H_c`) be `U (·) Vᵀ` applied to `Ĥ` with its bottom-right block `Ĥ₂₂` replaced by `0`
(resp. with every block except `Ĥ₂₂` replaced by `0`). Then `X = H₀ + H_c`, `rank H₀ ≤ 2k`,
`X₁ H_cᵀ = 0`, `X₁ᵀ H_c = 0` and `⟨H₀, H_c⟩ = 0`.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, proof of Proposition 6.8, p. 19.

Formalization Notes: real matrices; indices are 0-based, so the top-left `k × k` block is
`i < k ∧ j < k`. The top-left block of `D` is any `k × k` matrix, not only a diagonal `Σ`
(diagonality is not used by the claim): this is stronger than the construction on the page.
The hypothesis `X ∈ ker S` of the page is not used by this step and is dropped (stronger). -/
theorem block_decomposition {n p : ℕ} (k : ℕ) (X X₁ : Matrix (Fin n) (Fin p) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (V : Matrix (Fin p) (Fin p) ℝ) (D : Matrix (Fin n) (Fin p) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hD : ∀ (i : Fin n) (j : Fin p), ¬ ((i : ℕ) < k ∧ (j : ℕ) < k) → D i j = 0)
    (hX₁ : X₁ = U * D * Vᵀ) :
    let Hh : Matrix (Fin n) (Fin p) ℝ := Uᵀ * X * V
    let H0 : Matrix (Fin n) (Fin p) ℝ :=
      U * Matrix.of (fun (i : Fin n) (j : Fin p) =>
        if (i : ℕ) < k ∨ (j : ℕ) < k then Hh i j else 0) * Vᵀ
    let Hc : Matrix (Fin n) (Fin p) ℝ :=
      U * Matrix.of (fun (i : Fin n) (j : Fin p) =>
        if (i : ℕ) < k ∨ (j : ℕ) < k then 0 else Hh i j) * Vᵀ
    X = H0 + Hc ∧ H0.rank ≤ 2 * k ∧ X₁ * Hcᵀ = 0 ∧ X₁ᵀ * Hc = 0 ∧ traceInner H0 Hc = 0 := by sorry

end IRLSM.RIP
