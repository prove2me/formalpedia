-- Prove2me | Theorems.Thm_NesterovFB_Rates_eq9_prox_grad_inequality
-- name    : NesterovFB.Rates.eq9_prox_grad_inequality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T04:43:16.84432+00:00
-- url     : https://prove2.me/theorems/0ee55b13-51e4-4fa0-a5bc-999e78497cf3
-- title:
--   (9), p. 2 — Θ(y − sG_s(y)) ≤ Θ(x) + ⟨G_s(y), y − x⟩ − (s/2)‖G_s(y)‖² when s ≤ 1/L
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $\Psi:\mathcal H\to\mathbb R\cup\{+\infty\}$ proper, lower semicontinuous and convex, and $\Phi:\mathcal H\to\mathbb R$ convex and continuously differentiable with $L$-Lipschitz gradient. Let $\Theta=\Psi+\Phi$, let $s>0$ with $sL\le 1$, and let $G_s(y)=\frac1s\big(y-\operatorname{prox}_{s\Psi}(y-s\nabla\Phi(y))\big)$. Then for all $x,y\in\mathcal H$,
--   $$\Theta\big(y-sG_s(y)\big)\le\Theta(x)+\langle G_s(y),\,y-x\rangle-\frac s2\|G_s(y)\|^2 .$$
--
--   This is the basic one-step inequality of the proximal-gradient (forward-backward) step; applied at $y=y_k$ with $x=x_k$ and $x=x^*$ it yields (10) and (11), from which the Lyapunov estimate (13) and the velocity estimate (14) follow.
--
--   **Formalization Note.** The step condition is $sL\le1$, the paper's "since $s\le 1/L$", written without a division so that $L=0$ is allowed. $\operatorname{prox}_{s\Psi}$ is a map $P$ with `IsProx s Ψ P`. Both sides are extended reals; when $\Theta(x)=+\infty$ the inequality is trivially true, as on the page.
-- source:
--   Attouch and Peypouquet, The Rate of Convergence of Nesterov's Accelerated Forward-Backward Method is Actually Faster than 1/k^2, arXiv:1510.08740v4, p. 2, (9)

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_NesterovFB_Rates_Algorithm

open Filter Topology InnerProductSpace

namespace NesterovFB.Rates

theorem eq9_prox_grad_inequality {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ψ : H → EReal) (Φ : H → ℝ) (L : NNReal) (s : ℝ) (P : H → H)
    (hΨ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Ψ)
    (hΦc : ConvexOn ℝ Set.univ Φ) (hΦd : ContDiff ℝ 1 Φ)
    (hL : LipschitzWith L (gradient Φ))
    (hs : 0 < s) (hsL' : s * L ≤ 1)
    (hP : ThreeOpSplitting.ConvexRates.IsProx s Ψ P) :
    ∀ x y : H, theta Ψ Φ (y - s • gradMap Φ P s y) ≤ theta Ψ Φ x
      + ((⟪gradMap Φ P s y, y - x⟫_ℝ - s / 2 * ‖gradMap Φ P s y‖ ^ 2 : ℝ) : EReal) := by sorry

end NesterovFB.Rates
