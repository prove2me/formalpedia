-- Prove2me | Theorems.Thm_GeomDL_Filters_spectral_eq_polynomial_filter
-- name    : GeomDL.Filters.spectral_eq_polynomial_filter
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T18:14:16.611291+00:00
-- url     : https://prove2.me/theorems/677c3005-56b2-462f-88e1-bb6e3c344f5a
-- title:
--   §4.6, p. 64 — Σₖ αₖΔᵏX = Φ diag(p̂(λ₁), …, p̂(λₙ)) X̂ when Δ = ΦΛΦᵀ
-- statement:
--   Let $W\in\mathbb R^{n\times n}$ have Laplacian $\Delta=D-W$, and suppose $\Delta=\Phi\Lambda\Phi^\top$ with $\Phi$ orthogonal and $\Lambda=\operatorname{diag}(\lambda_1,\dots,\lambda_n)$. Let $r\ge 0$, $\alpha_0,\dots,\alpha_r\in\mathbb R$, $\hat p(\lambda)=\sum_{k=0}^r\alpha_k\lambda^k$, and $X\in\mathbb R^{n\times d}$ with Fourier coefficients $\hat X=\Phi^\top X$. Then
--   $$\sum_{k=0}^r\alpha_k\Delta^kX=\Phi\operatorname{diag}\big(\hat p(\lambda_1),\dots,\hat p(\lambda_n)\big)\hat X .$$
--
--   So the polynomial filter of Defferrard et al. is the spectral filter with transfer function $\hat p$, computed without an eigendecomposition.
--
--   **Formalization Note** The page's spectral filter $\hat p(\Delta)X=\Phi\hat p(\Lambda)\Phi^\top X$ is stated for a general transfer function; the theorem covers the polynomial transfer functions of the page's second display, for which both sides are defined independently of the eigendecomposition.
-- source:
--   Bronstein, Bruna, Cohen & Veličković, Geometric Deep Learning (arXiv:2104.13478v2), §4.6, p. 64, the displays for ˆp(∆)X

import Mathlib
import Definitions.Def_GeomDL_Filters_Defs

namespace GeomDL.Filters
open Matrix
/-- §4.6, p. 64: if `Δ = ΦΛΦᵀ` with `Φ` orthogonal and `Λ = diag(λ₁, …, λₙ)`, then the
polynomial filter `∑_{k=0}^r α_k Δ^k X` equals the spectral filter
`Φ diag(p̂(λ₁), …, p̂(λₙ)) X̂` with `X̂ = ΦᵀX` and `p̂(λ) = ∑_{k=0}^r α_k λ^k`. -/
theorem spectral_eq_polynomial_filter {n d : ℕ} (W : Matrix (Fin n) (Fin n) ℝ)
    (Φ : Matrix (Fin n) (Fin n) ℝ) (hΦ : Φ ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (lam : Fin n → ℝ) (hΔ : lap W = Φ * Matrix.diagonal lam * Φᵀ)
    (r : ℕ) (α : Fin (r + 1) → ℝ) (X : Matrix (Fin n) (Fin d) ℝ) :
    polyFilter W r α * X = Φ * Matrix.diagonal (fun i => polyEval α (lam i)) * (Φᵀ * X) := by sorry
end GeomDL.Filters
