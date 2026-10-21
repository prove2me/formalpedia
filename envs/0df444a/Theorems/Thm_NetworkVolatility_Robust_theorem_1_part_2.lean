-- Prove2me | Theorems.Thm_NetworkVolatility_Robust_theorem_1_part_2
-- name    : NetworkVolatility.Robust.theorem_1_part_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:57.451985+00:00
-- url     : https://prove2.me/theorems/56140a16-0709-4f5a-af39-7ab4abad425a
-- title:
--   Proof of Theorem 1, Part 2, p. 12 — $\tilde W=(1+\epsilon)W$ and the top eigenvector attain $\alpha\lambda_{\max}\epsilon/(1-\alpha(1+\epsilon)\lambda_{\max})$
-- statement:
--   Assume the standing assumptions, $\epsilon\ge0$ and condition (1), $\alpha\lambda_{\max}(1+\epsilon)<1$, where $\lambda_{\max}=\lambda_{\max}(W)$. Let $v\neq0$ be an eigenvector of $W$ for the eigenvalue $\lambda_{\max}$, i.e. $Wv=\lambda_{\max}v$, and let $\tilde W=(1+\epsilon)W$. Then $\tilde W\in\mathcal W(W,\epsilon)$ and
--   $$\frac{\big|v^\top(I-\alpha W)^{-1}v-v^\top(I-\alpha\tilde W)^{-1}v\big|}{v^\top(I-\alpha W)^{-1}v}=\frac{\alpha\lambda_{\max}\epsilon}{1-\alpha(1+\epsilon)\lambda_{\max}} .$$
--
--   With $b-c\mathbf 1=v$, Proposition 2 turns the left side into the relative revenue change $|R(W,\alpha,b)-R(\tilde W,\alpha,b)|/R(W,\alpha,b)$, so this computation is the lower-bound half of Theorem 1.
--
--   **Formalization Note** The statement is the matrix computation of p. 12, without the substitution $b=c\mathbf 1+v_{\max}$: that $b$ satisfies $b>c\mathbf 1$ only when $v_{\max}$ is strictly positive, which is why Theorem 1 is stated with a least upper bound.
-- source:
--   Baron, Hu & Malekian, Revenue volatility under uncertain network effects, SSRN preprint 3561270 (version of 2020-03-25), p. 12, proof of Theorem 1, Part 2

import Mathlib
import Definitions.Def_NetworkVolatility_Robust_Model

namespace NetworkVolatility.Robust

open Matrix

/-- Proof of Theorem 1, Part 2, p. 12 (lower bound). Under the standing assumptions, `ε ≥ 0` and
condition (1), let `v ≠ 0` be an eigenvector of `W` for the eigenvalue `λmax`. Then
`W̃ = (1 + ε)W ∈ 𝒲(W, ε)` and
`|vᵀ(I - αW)⁻¹v - vᵀ(I - αW̃)⁻¹v| / vᵀ(I - αW)⁻¹v = αλmaxε / (1 - α(1 + ε)λmax)`. -/
theorem theorem_1_part_2 {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (α ε : ℝ)
    (hS : Standing W α) (hε : 0 ≤ ε) (h1 : α * lamMax W * (1 + ε) < 1)
    (v : Fin n → ℝ) (hv : v ≠ 0) (hev : W *ᵥ v = lamMax W • v) :
    (1 + ε) • W ∈ uncSet W ε ∧
    |v ⬝ᵥ ((1 - α • W)⁻¹ *ᵥ v) - v ⬝ᵥ ((1 - α • ((1 + ε) • W))⁻¹ *ᵥ v)| /
        (v ⬝ᵥ ((1 - α • W)⁻¹ *ᵥ v)) =
      α * lamMax W * ε / (1 - α * (1 + ε) * lamMax W) := by sorry

end NetworkVolatility.Robust
