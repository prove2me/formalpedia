-- Prove2me | Theorems.Thm_ModernOnlineLearning_FTRL_lemma_7_5
-- name    : ModernOnlineLearning.FTRL.lemma_7_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:37:42.42299+00:00
-- url     : https://prove2.me/theorems/23d3215f-cd10-4a12-aa3c-3c0d8073e4ec
-- title:
--   Lemma 7.5, p. 101 — existence, uniqueness, and FTRL stability
-- statement:
--   Let $V$ be nonempty, closed and convex. Suppose $F_t$ is closed, subdifferentiable and strongly convex on $V$. Then it has a unique minimizer $x_t$. Suppose also that $F_t+\ell_t$ is closed, subdifferentiable and $\lambda_t$-strongly convex on $V$, with $\lambda_t>0$. For any minimizer $x_{t+1}$ of $F_{t+1}$ and any subgradient $g_t\in\partial\ell_t(x_t)$,
--   $$F_t(x_t)-F_{t+1}(x_{t+1})+\ell_t(x_t)\le g_t(x_t-x_{t+1})-\frac{\lambda_t}{2}\|x_t-x_{t+1}\|^2+\psi_t(x_{t+1})-\psi_{t+1}(x_{t+1})\le\frac{\|g_t\|_*^2}{2\lambda_t}+\psi_t(x_{t+1})-\psi_{t+1}(x_{t+1}).$$
--   This bounds the change in objective values by the dual norm of a loss subgradient and the change in regularizer.
--
--   **Formalization Note** Existence of $x_{t+1}$ is stated by quantifying over any such minimizer; the lemma's existence assertion concerns $x_t$. Subgradients are full-space continuous linear functionals. The positivity of $\lambda_t$ makes the printed denominator meaningful.
-- source:
--   Orabona, arXiv:1912.13213v10, Lemma 7.5, p. 101

import Mathlib
import Definitions.Def_ModernOnlineLearning_FTRL_Defs

set_option autoImplicit false

namespace ModernOnlineLearning.FTRL

/-- Orabona, Lemma 7.5, p. 101: existence, uniqueness, and the FTRL stability chain. -/
theorem lemma_7_5
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (V : Set E) (hVclosed : IsClosed V) (hVconvex : Convex ℝ V)
    (hVnonempty : V.Nonempty) (ψ ℓ : ℕ → E → ℝ) (t : ℕ) (ht : 1 ≤ t)
    (lam : ℝ) (hlam : 0 < lam)
    (hFtClosed : IsClosedFunctionOn V (F ψ ℓ t))
    (hFtSubdiff : IsSubdifferentiableOn V (F ψ ℓ t))
    (hFtStrong : ∃ κ : ℝ, 0 < κ ∧ StrongConvexOn V κ (F ψ ℓ t))
    (hFtlClosed : IsClosedFunctionOn V (fun y => F ψ ℓ t y + ℓ t y))
    (hFtlSubdiff : IsSubdifferentiableOn V (fun y => F ψ ℓ t y + ℓ t y))
    (hFtlStrong : StrongConvexOn V lam (fun y => F ψ ℓ t y + ℓ t y)) :
    (∃! z : E, IsMinimizerOn V (F ψ ℓ t) z) ∧
    ∀ (x y : E), IsMinimizerOn V (F ψ ℓ t) x →
      IsMinimizerOn V (F ψ ℓ (t + 1)) y →
      (∃ g : E →L[ℝ] ℝ, IsSubgradientAt (ℓ t) x g) →
      ∀ g : E →L[ℝ] ℝ, IsSubgradientAt (ℓ t) x g →
      F ψ ℓ t x - F ψ ℓ (t + 1) y + ℓ t x ≤
        g (x - y) - lam / 2 * ‖x - y‖ ^ 2 + ψ t y - ψ (t + 1) y ∧
      g (x - y) - lam / 2 * ‖x - y‖ ^ 2 + ψ t y - ψ (t + 1) y ≤
        ‖g‖ ^ 2 / (2 * lam) + ψ t y - ψ (t + 1) y := by sorry

end ModernOnlineLearning.FTRL
