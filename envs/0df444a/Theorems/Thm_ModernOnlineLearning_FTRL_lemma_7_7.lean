-- Prove2me | Theorems.Thm_ModernOnlineLearning_FTRL_lemma_7_7
-- name    : ModernOnlineLearning.FTRL.lemma_7_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:37:09.343579+00:00
-- url     : https://prove2.me/theorems/75cc5c26-8fca-40f3-8e8a-aab2809a9fab
-- title:
--   Lemma 7.7, pp. 102–103 — proximal regularizers
-- statement:
--   Let $V$ be nonempty, closed and convex. Suppose $F_{t+1}$ is closed, subdifferentiable and $\lambda_{t+1}$-strongly convex on $V$, with $\lambda_{t+1}>0$. Let $x_t$ be an FTRL minimizer that also minimizes $\psi_{t+1}-\psi_t$ on $V$. Then $F_{t+1}$ has a unique minimizer $x_{t+1}$. For every $g_t\in\partial\ell_t(x_t)$,
--   $$F_t(x_t)-F_{t+1}(x_{t+1})+\ell_t(x_t)\le g_t(x_t-x_{t+1})-\frac{\lambda_{t+1}}2\|x_t-x_{t+1}\|^2+\psi_t(x_t)-\psi_{t+1}(x_t)\le\frac{\|g_t\|_*^2}{2\lambda_{t+1}}+\psi_t(x_t)-\psi_{t+1}(x_t).$$
--   The proximal condition evaluates the regularizer change at the current iterate and provides a second stability bound for FTRL.
--
--   **Formalization Note** The existence assertion is explicit. The book's nonempty subdifferential hypothesis is represented before universally quantifying over its elements.
-- source:
--   Orabona, arXiv:1912.13213v10, Lemma 7.7, pp. 102–103

import Mathlib
import Definitions.Def_ModernOnlineLearning_FTRL_Defs

set_option autoImplicit false

namespace ModernOnlineLearning.FTRL

/-- Orabona, Lemma 7.7, pp. 102–103: the proximal-regularizer stability chain. -/
theorem lemma_7_7
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (V : Set E) (hVclosed : IsClosed V) (hVconvex : Convex ℝ V)
    (hVnonempty : V.Nonempty) (ψ ℓ : ℕ → E → ℝ) (t : ℕ) (ht : 1 ≤ t)
    (lam : ℝ) (hlam : 0 < lam)
    (hFnextClosed : IsClosedFunctionOn V (F ψ ℓ (t + 1)))
    (hFnextSubdiff : IsSubdifferentiableOn V (F ψ ℓ (t + 1)))
    (hFnextStrong : StrongConvexOn V lam (F ψ ℓ (t + 1)))
    (x : E) (hx : IsMinimizerOn V (F ψ ℓ t) x)
    (hprox : IsMinimizerOn V (fun z => ψ (t + 1) z - ψ t z) x) :
    (∃! y : E, IsMinimizerOn V (F ψ ℓ (t + 1)) y) ∧
    ∀ y : E, IsMinimizerOn V (F ψ ℓ (t + 1)) y →
      (∃ g : E →L[ℝ] ℝ, IsSubgradientAt (ℓ t) x g) →
      ∀ g : E →L[ℝ] ℝ, IsSubgradientAt (ℓ t) x g →
      F ψ ℓ t x - F ψ ℓ (t + 1) y + ℓ t x ≤
        g (x - y) - lam / 2 * ‖x - y‖ ^ 2 + ψ t x - ψ (t + 1) x ∧
      g (x - y) - lam / 2 * ‖x - y‖ ^ 2 + ψ t x - ψ (t + 1) x ≤
        ‖g‖ ^ 2 / (2 * lam) + ψ t x - ψ (t + 1) x := by sorry

end ModernOnlineLearning.FTRL
