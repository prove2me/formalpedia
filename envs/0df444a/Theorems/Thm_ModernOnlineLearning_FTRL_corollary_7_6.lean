-- Prove2me | Theorems.Thm_ModernOnlineLearning_FTRL_corollary_7_6
-- name    : ModernOnlineLearning.FTRL.corollary_7_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:37:08.211095+00:00
-- url     : https://prove2.me/theorems/506a762d-28df-4126-8d82-cbd1cdde8335
-- title:
--   Corollary 7.6, p. 102 — adaptive and square-root FTRL regret bounds
-- statement:
--   Let $V$ be nonempty, closed and convex, and let the closed function $\psi$ be $\mu$-strongly convex on $V$, where $\mu>0$. Write $m=\min_{z\in V}\psi(z)$, and use the regularizers $\psi_t(z)=(\psi(z)-m)/\eta_{t-1}$ for $t=1,\ldots,T$, with $\psi_{T+1}=\psi_T$ and positive step sizes. Let $x_t$ be any FTRL run and suppose each loss is subdifferentiable on $V$. Then for every $u\in V$ and every sequence of subgradients $g_t\in\partial\ell_t(x_t)$,
--   $$\sum_{t=1}^T(\ell_t(x_t)-\ell_t(u))\le\frac{\psi(u)-m}{\eta_{T-1}}+\sum_{t=1}^T\frac{\eta_{t-1}}{2\mu}\|g_t\|_*^2+\sum_{t=1}^{T-1}\left(\frac1{\eta_{t-1}}-\frac1{\eta_t}\right)(\psi(x_{t+1})-m).$$
--   Moreover, if every loss is $L$-Lipschitz on an open neighborhood of $V$ and $\eta_{t-1}=\alpha\sqrt\mu/(L\sqrt t)$ for positive $\alpha,L$, then
--   $$\sum_{t=1}^T\ell_t(x_t)-\sum_{t=1}^T\ell_t(u)\le\left(\frac{\psi(u)-m}{\alpha}+\alpha\right)\frac{L\sqrt T}{\sqrt\mu}.$$
--   The first statement retains the effect of changes in the regularizer; the second gives the chapter's explicit square-root regret rate.
--
--   **Formalization Note** Rounds begin at $1$ and step sizes at $0$. The minimum $m$ is supplied by a minimizing point; the existence of that point and of the run is implicit in the book. Losses are real-valued on the ambient space. The book's subdifferentiability is represented by full-space subgradients at every point of $V$. Positivity of $\mu$, $\alpha$, $L$, and the used step sizes excludes zero denominators; $T\ge1$ excludes an empty schedule.
-- source:
--   Orabona, arXiv:1912.13213v10, Corollary 7.6, p. 102

import Mathlib
import Definitions.Def_ModernOnlineLearning_FTRL_Defs

set_option autoImplicit false

namespace ModernOnlineLearning.FTRL

/-- Orabona, Corollary 7.6, p. 102: both the adaptive and square-root-schedule bounds. -/
theorem corollary_7_6
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (V : Set E) (hVclosed : IsClosed V) (hVconvex : Convex ℝ V)
    (hVnonempty : V.Nonempty) (ψ : E → ℝ)
    (hψclosed : IsClosedFunctionOn V ψ)
    (mu : ℝ) (hmu : 0 < mu) (hψstrong : StrongConvexOn V mu ψ)
    (z₀ : E) (hz₀ : IsMinimizerOn V ψ z₀)
    (ℓ : ℕ → E → ℝ) (η : ℕ → ℝ) (T : ℕ) (hT : 1 ≤ T)
    (hη : ∀ s < T, 0 < η s)
    (x : ℕ → E)
    (hRun : IsFTRLRunUpTo V (scheduledRegularizer ψ (ψ z₀) η T) ℓ x T)
    (hSubdiff : ∀ t ∈ Finset.Icc 1 T, IsSubdifferentiableOn V (ℓ t)) :
    (∀ g : ℕ → (E →L[ℝ] ℝ),
      (∀ t ∈ Finset.Icc 1 T, IsSubgradientAt (ℓ t) (x t) (g t)) →
      ∀ u ∈ V,
        (∑ t ∈ Finset.Icc 1 T, (ℓ t (x t) - ℓ t u)) ≤
          (ψ u - ψ z₀) / η (T - 1) +
          (∑ t ∈ Finset.Icc 1 T, η (t - 1) / (2 * mu) * ‖g t‖ ^ 2) +
          (∑ t ∈ Finset.Icc 1 (T - 1),
            (1 / η (t - 1) - 1 / η t) * (ψ (x (t + 1)) - ψ z₀))) ∧
    (∀ (α L : ℝ), 0 < α → 0 < L →
      (∀ t ∈ Finset.Icc 1 T, IsLipschitzOnOpenNeighborhood V (ℓ t) L) →
      (∀ t ∈ Finset.Icc 1 T,
        η (t - 1) = α * Real.sqrt mu / (L * Real.sqrt (t : ℝ))) →
      ∀ u ∈ V,
        (∑ t ∈ Finset.Icc 1 T, ℓ t (x t)) -
          (∑ t ∈ Finset.Icc 1 T, ℓ t u) ≤
          ((ψ u - ψ z₀) / α + α) * (L * Real.sqrt (T : ℝ) / Real.sqrt mu)) := by sorry

end ModernOnlineLearning.FTRL
