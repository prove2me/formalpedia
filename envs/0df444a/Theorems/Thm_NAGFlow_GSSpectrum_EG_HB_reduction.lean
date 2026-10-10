-- Prove2me | Theorems.Thm_NAGFlow_GSSpectrum_EG_HB_reduction
-- name    : NAGFlow.GSSpectrum.EG_HB_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:44:43.81835+00:00
-- url     : https://prove2.me/theorems/c20aab90-d2fc-4934-833e-f85bfd79486d
-- title:
--   App. A, p. 36 — E(α, G_HB) in closed block form, and θ ∈ σ(E(α, G_HB)) ⇔ θ ∈ σ(E(α, R(λ))) for some λ ∈ σ(A)
-- statement:
--   Let $A$ be a real symmetric $d\times d$ matrix, $\mu>0$, $\alpha>0$, and let $E(\alpha,G)$ be the block Gauss–Seidel matrix (42) of
--   $G_{\mathrm{HB}}=\begin{pmatrix}0 & I\\ -A/\mu & -2I\end{pmatrix}$. Then
--   $$E(\alpha,G_{\mathrm{HB}})=\frac{1}{1+2\alpha}\begin{pmatrix}(1+2\alpha)I & \alpha(1+2\alpha)I\\ -\alpha A/\mu & I-A\alpha^2/\mu\end{pmatrix},$$
--   and for every complex $\theta$,
--   $$\theta\in\sigma(E(\alpha,G_{\mathrm{HB}}))\iff \theta\in\sigma(E(\alpha,R(\lambda)))\ \text{for some }\lambda\in\sigma(A),\qquad R(\lambda)=\begin{pmatrix}0&1\\-\lambda/\mu&-2\end{pmatrix},$$
--   where $E(\alpha,R(\lambda))$ is the $2\times2$ Gauss–Seidel matrix of (124).
--
--   This reduces the spectrum of the $2d\times2d$ iteration matrix to the spectra of $d$ explicit $2\times2$ matrices, one per eigenvalue of $A$, to which Lemma A.1 applies.
--
--   **Formalization Note.** The paper says "it is clear that" for the equivalence; it rests on the orthogonal diagonalisation of the symmetric matrix $A$. Only symmetry of $A$, $\mu>0$ and $\alpha>0$ are assumed; the eigenvalue bounds of the quadratic model are not needed for this statement.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, App. A, proof of Theorem 2.1, displays after Lemma A.1, p. 36

import Mathlib
import Definitions.Def_NAGFlow_GSSpectrum_Setting

namespace NAGFlow.GSSpectrum

open Matrix

/-- App. A, p. 36. For a real symmetric A, μ > 0 and α > 0, the Gauss–Seidel matrix of G_HB is
E(α, G_HB) = (1/(1 + 2α))((1 + 2α)I, α(1 + 2α)I ; −αA/μ, I − Aα²/μ), and
θ ∈ σ(E(α, G_HB)) ⟺ θ ∈ σ(E(α, R(λ))) for some λ ∈ σ(A), where R(λ) = (0 1 ; −λ/μ −2). -/
theorem EG_HB_reduction {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (μ α : ℝ) (hA : A.IsHermitian)
    (hμ : 0 < μ) (hα : 0 < α) :
    EG α (GHB A μ) = (1 / (1 + 2 * α)) •
        fromBlocks ((1 + 2 * α) • (1 : Matrix (Fin d) (Fin d) ℝ))
          ((α * (1 + 2 * α)) • (1 : Matrix (Fin d) (Fin d) ℝ))
          (-((α / μ) • A)) (1 - (α ^ 2 / μ) • A) ∧
      ∀ θ : ℂ, θ ∈ cspec (EG α (GHB A μ)) ↔
        ∃ lam ∈ spectrum ℝ A, θ ∈ cspec (ER α (RHB lam μ)) := by sorry

end NAGFlow.GSSpectrum
