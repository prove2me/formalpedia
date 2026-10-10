-- Prove2me | Theorems.Thm_NAGFlow_GSSpectrum_rho_NAG
-- name    : NAGFlow.GSSpectrum.rho_NAG
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:41:46.528791+00:00
-- url     : https://prove2.me/theorems/83484290-d845-4c0f-a85e-ad8dbb14417d
-- title:
--   App. A, p. 36 — under (127), ρ(E(α, G_NAG)) = max over λ ∈ σ(A) of ρ(E(α, R(λ))) = 1/√(1 + 2α + α²) ≤ 1/√(1 + 2α)
-- statement:
--   Let $A$ be a real symmetric matrix with $0<\mu=\lambda_{\min}(A)$, $L=\lambda_{\max}(A)$ and $\kappa(A)=L/\mu$, and for $\lambda\in\sigma(A)$ let $R(\lambda)=\begin{pmatrix}-1&1\\1-\lambda/\mu&-1\end{pmatrix}$, the $2\times2$ reduction of
--   $G_{\mathrm{NAG}}=\begin{pmatrix}-I & I\\ I-A/\mu & -I\end{pmatrix}$. If $0<\alpha\le2/\sqrt{\kappa(A)}$ (condition (127)), then
--   $$\rho(E(\alpha,G_{\mathrm{NAG}}))=\max_{\lambda\in\sigma(A)}\rho(E(\alpha,R(\lambda)))=\frac{1}{\sqrt{1+2\alpha+\alpha^2}}\le\frac{1}{\sqrt{1+2\alpha}}.$$
--   More precisely, each $\rho(E(\alpha,R(\lambda)))$ equals $1/\sqrt{1+2\alpha+\alpha^2}$, $\rho(E(\alpha,G_{\mathrm{NAG}}))$ equals it, and every eigenvalue of $E(\alpha,G_{\mathrm{NAG}})$ has exactly this modulus.
--
--   This is the NAG half of Theorem 2.1.
--
--   **Formalization Note.** The page says "Similarly" and does not print $R(\lambda)$ for this case; the matrix used is $R_{\mathrm{NAG}}$ of the proof of Proposition 2.1 (p. 9) with $\theta=\lambda/\mu$. The middle "max" is rendered as in the heavy-ball statement. Eigenvalues are complex.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, App. A, proof of Theorem 2.1, display after "Similarly, for G = G_NAG", p. 36; R_NAG from the proof of Proposition 2.1, p. 9

import Mathlib
import Definitions.Def_NAGFlow_GSSpectrum_Setting

namespace NAGFlow.GSSpectrum

open Matrix

/-- App. A, p. 36, the G_NAG case. In the quadratic model with μ > 0, if 0 < α ≤ 2/√κ(A) (127),
then ρ(E(α, G_NAG)) = max_{λ ∈ σ(A)} ρ(E(α, R(λ))) = 1/√(1 + 2α + α²) ≤ 1/√(1 + 2α), where
R(λ) = (−1 1 ; 1 − λ/μ −1); in fact every eigenvalue of E(α, G_NAG) has modulus
1/√(1 + 2α + α²). -/
theorem rho_NAG {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (μ L α : ℝ) (hA : IsQuadModel A μ L)
    (hμ : 0 < μ) (hα : 0 < α) (h127 : α ≤ 2 / Real.sqrt (kappa μ L)) :
    (∀ lam ∈ spectrum ℝ A,
        IsSpecRadius (ER α (RNAG lam μ)) (1 / Real.sqrt (1 + 2 * α + α ^ 2))) ∧
      IsSpecRadius (EG α (GNAG A μ)) (1 / Real.sqrt (1 + 2 * α + α ^ 2)) ∧
      (∀ z ∈ cspec (EG α (GNAG A μ)), ‖z‖ = 1 / Real.sqrt (1 + 2 * α + α ^ 2)) ∧
      1 / Real.sqrt (1 + 2 * α + α ^ 2) ≤ 1 / Real.sqrt (1 + 2 * α) := by sorry

end NAGFlow.GSSpectrum
