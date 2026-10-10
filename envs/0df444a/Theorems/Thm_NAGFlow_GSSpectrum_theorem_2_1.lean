-- Prove2me | Theorems.Thm_NAGFlow_GSSpectrum_theorem_2_1
-- name    : NAGFlow.GSSpectrum.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:41:55.07078+00:00
-- url     : https://prove2.me/theorems/2313a840-b93d-443a-ac3d-f00deddaf68a
-- title:
--   Theorem 2.1, p. 10 — for G = G_HB or G_NAG and 0 < α ≤ 2/√κ(A), the Gauss–Seidel scheme (41) is A-stable and ρ(E(α, G)) ≤ 1/√(1 + 2α)
-- statement:
--   Let $A$ be a real symmetric $d\times d$ matrix whose eigenvalues satisfy $0<\mu=\lambda_{\min}(A)\le\lambda\le\lambda_{\max}(A)=L$, and let $\kappa(A)=L/\mu$. Let $G$ be either of the transformations (39),
--   $$G_{\mathrm{HB}}=\begin{pmatrix}0 & I\\ -A/\mu & -2I\end{pmatrix},\qquad G_{\mathrm{NAG}}=\begin{pmatrix}-I & I\\ I-A/\mu & -I\end{pmatrix},$$
--   split blockwise as $G=M+N$ with $M$ the lower triangular part (diagonal blocks included), and let $E(\alpha,G)=(I-\alpha M)^{-1}(I+\alpha N)$ be the one-step matrix of the Gauss–Seidel splitting scheme $(y_{k+1}-y_k)/\alpha=My_{k+1}+Ny_k$ of (41). If
--   $$0<\alpha\le\frac{2}{\sqrt{\kappa(A)}},$$
--   then the scheme is A-stable, $\rho(E(\alpha,G))<1$, and
--   $$\rho(E(\alpha,G))\le\frac{1}{\sqrt{1+2\alpha}}.$$
--
--   With $\alpha=2/\sqrt{\kappa(A)}$ this gives the contraction factor $1-O(1/\sqrt{\kappa(A)})$ per step, the accelerated rate, for an explicit scheme that never inverts $A$.
--
--   **Formalization Note.** Eigenvalues of the non-symmetric real matrix $E(\alpha,G)$ are complex. "$\rho(E)<1$" and "$\rho(E)\le r$" are stated for every eigenvalue $z$: $|z|<1$ and $|z|\le r$. This avoids a junk supremum; $\sigma(E)$ is nonempty here anyway since $d\ge1$. $\mu=\lambda_{\min}(A)$ and $L=\lambda_{\max}(A)$ are encoded as: both are eigenvalues of $A$ and bound all eigenvalues of $A$. The case $\mu>0$ is the one of Section 2.3, where $G_{\mathrm{HB}}$ and $G_{\mathrm{NAG}}$ are defined.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, Theorem 2.1, p. 10 (with (39) p. 9, (41)–(42) p. 10); proof in App. A, pp. 35–36

import Mathlib
import Definitions.Def_NAGFlow_GSSpectrum_Setting

namespace NAGFlow.GSSpectrum

open Matrix

/-- Theorem 2.1, p. 10. In the quadratic model of Section 2 with μ = λ_min(A) > 0, for
G = G_HB or G_NAG of (39), if 0 < α ≤ 2/√κ(A), then the Gauss–Seidel splitting scheme (41) is
A-stable, i.e. ρ(E(α, G)) < 1, and ρ(E(α, G)) ≤ 1/√(1 + 2α). Both spectral-radius claims are
stated eigenvalue by eigenvalue. -/
theorem theorem_2_1 {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (μ L α : ℝ) (hA : IsQuadModel A μ L)
    (hμ : 0 < μ) (hα : 0 < α) (h127 : α ≤ 2 / Real.sqrt (kappa μ L)) :
    ∀ G, (G = GHB A μ ∨ G = GNAG A μ) →
      (∀ z ∈ cspec (EG α G), ‖z‖ < 1) ∧
        ∀ z ∈ cspec (EG α G), ‖z‖ ≤ 1 / Real.sqrt (1 + 2 * α) := by sorry

end NAGFlow.GSSpectrum
