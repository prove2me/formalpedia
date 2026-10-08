-- Prove2me | Theorems.Thm_IRLSM_Convergence_lemma_5_2
-- name    : IRLSM.Convergence.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:52:41.742123+00:00
-- url     : https://prove2.me/theorems/5a9a5c09-5b33-4c95-a136-d7caa16b5056
-- title:
--   Lemma 5.2 — derivative of $\mathcal J$ in $W$: $\partial_W\mathcal J(X,W)=\tfrac12(XX^*-W^{-2})$
-- statement:
--   Let $X$ be $n\times p$ and $W=W^{\mathsf T}\succ0$. For every symmetric direction $V=V^{\mathsf T}$, the function $h\mapsto\mathcal J(X,W+hV)$ is differentiable at $h=0$ and
--   $$\frac{d}{dh}\Big|_{h=0}\mathcal J(X,W+hV)=\tfrac12\big\langle XX^{\mathsf T}-W^{-2},V\big\rangle .$$
--   Thus the derivative of $\mathcal J$ in its second variable, along symmetric matrices, is $\tfrac12(XX^{\mathsf T}-W^{-2})$.
--
--   The derivative identifies the stationary weights of $\mathcal J(X,\cdot)$, which the proof of Proposition 5.3 uses through the KKT conditions (5.9).
--
--   **Formalization Note** Matrices are real ($n\times p$, with the paper's standing assumption $n\le p$ where $n\times n$ objects occur); the measurement map is $\mathcal S(X)_l=\langle A_l,X\rangle$ for measurement matrices $A_1,\dots,A_m$, so $\mathcal S^*$ is $u\mapsto\sum_l u_lA_l$ and $\langle\cdot,\cdot\rangle$ is the trace inner product. The derivative is stated in Gâteaux form along symmetric directions, which is what the page's proof computes. The page's (5.5) reads $\partial_W\mathcal J(X,W)=XX^*-W^{-2}$; since $\mathcal J$ carries the factor $\tfrac12$ of (5.1), the derivative of $\mathcal J$ as defined is $\tfrac12(XX^*-W^{-2})$, which is stated here. Only the zero set of the derivative is used later.
-- source:
--   Fornasier, Rauhut, Ward, Low-rank matrix recovery via iteratively reweighted least squares minimization, arXiv:1010.2471v4 (2011), Lemma 5.2, (5.5), p. 13 (proof pp. 13–14)

import Mathlib
import Definitions.Def_IRLSM_Convergence_Algorithm

open HighDimStat.MatrixRank Matrix

namespace IRLSM.Convergence

/-- **Lemma 5.2 (derivative of 𝒥 in W).** For `W = Wᵀ ≻ 0` and every symmetric direction `V`, the
function `h ↦ 𝒥(X, W + hV)` is differentiable at `h = 0` with derivative
`½ ⟨X Xᵀ − W⁻², V⟩`, i.e. `∂_W 𝒥(X, W) = ½ (X Xᵀ − W⁻²)` along symmetric directions.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, Lemma 5.2, (5.5), p. 13 (proof pp. 13–14).

Formalization Notes: real matrices. The derivative is stated in the Gâteaux form along symmetric
directions `V = Vᵀ`, which is what the page's proof computes ("Gâteaux differentiation with
respect to V = V*"). **Printed slip:** (5.5) reads `∂_W 𝒥(X, W) = X X* − W⁻²`, but `𝒥` carries the
factor `½` of (5.1), so its derivative is `½ (X X* − W⁻²)`, as stated here; (5.6)–(5.7) are the
derivatives of `‖W^{1/2}X‖²_F` and `‖W^{−1/2}‖²_F` without the `½`. Only the zero set of the
derivative is used later (KKT (5.9)). `n ≤ p` is the page's standing assumption (p. 4). -/
theorem lemma_5_2 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (W : Matrix (Fin n) (Fin n) ℝ)
    (hnp : n ≤ p) (hW : W.PosDef) :
    ∀ V : Matrix (Fin n) (Fin n) ℝ, V.IsHermitian →
      HasDerivAt (fun h : ℝ => J X (W + h • V))
        ((1 / 2) * traceInner (X * Xᵀ - W⁻¹ ^ 2) V) 0 := by sorry

end IRLSM.Convergence
