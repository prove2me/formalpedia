-- Prove2me | Theorems.Thm_NAGFlow_GSSpectrum_rho_HB
-- name    : NAGFlow.GSSpectrum.rho_HB
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:41:59.437367+00:00
-- url     : https://prove2.me/theorems/dd573cb8-cd30-4c59-8600-39cd19b8b4de
-- title:
--   App. A, p. 36 — under (127), ρ(E(α, G_HB)) = max over λ ∈ σ(A) of ρ(E(α, R(λ))) = 1/√(1 + 2α)
-- statement:
--   Let $A$ be a real symmetric matrix with $0<\mu=\lambda_{\min}(A)$, $L=\lambda_{\max}(A)$ and $\kappa(A)=L/\mu$, and let $R(\lambda)=\begin{pmatrix}0&1\\-\lambda/\mu&-2\end{pmatrix}$. Then $|\operatorname{tr}R(\lambda)|\le2\sqrt{\det R(\lambda)}$ for every $\lambda\in\sigma(A)$, and if
--   $$0<\alpha\le 2/\sqrt{\kappa(A)},\tag{127}$$
--   then
--   $$\rho(E(\alpha,G_{\mathrm{HB}}))=\max_{\lambda\in\sigma(A)}\rho(E(\alpha,R(\lambda)))=\frac{1}{\sqrt{1+2\alpha}}.$$
--   More precisely, $\rho(E(\alpha,R(\lambda)))=1/\sqrt{1+2\alpha}$ for every $\lambda\in\sigma(A)$, $\rho(E(\alpha,G_{\mathrm{HB}}))=1/\sqrt{1+2\alpha}$, and every eigenvalue of $E(\alpha,G_{\mathrm{HB}})$ has modulus exactly $1/\sqrt{1+2\alpha}$.
--
--   This is the heavy-ball half of Theorem 2.1, with the bound attained.
--
--   **Formalization Note.** The middle term "$\max_\lambda\rho(E(\alpha,R(\lambda)))$" is rendered by stating that each $\rho(E(\alpha,R(\lambda)))$ equals the common value; since $\sigma(A)$ is nonempty ($\mu\in\sigma(A)$), the maximum is that value. Eigenvalues of the real non-symmetric matrices are complex.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, App. A, proof of Theorem 2.1, (127) and the display after it, p. 36

import Mathlib
import Definitions.Def_NAGFlow_GSSpectrum_Setting

namespace NAGFlow.GSSpectrum

open Matrix

/-- App. A, p. 36, the G_HB case. In the quadratic model with μ > 0, |tr R(λ)| ≤ 2√(det R(λ)) for
every λ ∈ σ(A), and if 0 < α ≤ 2/√κ(A) (127), then
ρ(E(α, G_HB)) = max_{λ ∈ σ(A)} ρ(E(α, R(λ))) = 1/√(1 + 2α); in fact every eigenvalue of
E(α, G_HB) has modulus 1/√(1 + 2α). -/
theorem rho_HB {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (μ L α : ℝ) (hA : IsQuadModel A μ L)
    (hμ : 0 < μ) (hα : 0 < α) (h127 : α ≤ 2 / Real.sqrt (kappa μ L)) :
    (∀ lam ∈ spectrum ℝ A, |(RHB lam μ).trace| ≤ 2 * Real.sqrt (RHB lam μ).det) ∧
      (∀ lam ∈ spectrum ℝ A, IsSpecRadius (ER α (RHB lam μ)) (1 / Real.sqrt (1 + 2 * α))) ∧
      IsSpecRadius (EG α (GHB A μ)) (1 / Real.sqrt (1 + 2 * α)) ∧
      ∀ z ∈ cspec (EG α (GHB A μ)), ‖z‖ = 1 / Real.sqrt (1 + 2 * α) := by sorry

end NAGFlow.GSSpectrum
