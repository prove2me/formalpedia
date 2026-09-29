-- Prove2me | Theorems.Thm_MonopolesInstantonsConfinement_phi4Kink_isSoliton
-- name    : MonopolesInstantonsConfinement.phi4Kink_isSoliton
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:21:01.077898+00:00
-- url     : https://prove2.me/theorems/aa32e088-996b-4ecf-88f9-6a45e13b10cf
-- title:
--   The $\varphi^4$ kink is a static soliton from $-F$ to $F$
-- statement:
--   Let $\lambda > 0$, $F > 0$, $x_0 \in \mathbb R$, and let $m = \sqrt{\lambda F^2/3}$. The kink
--   $$\varphi_a(x) = F\tanh\big(\tfrac12 m (x - x_0)\big)$$
--   of the Mexican-hat potential $V_a(\varphi) = \frac{\lambda}{24}(\varphi^2 - F^2)^2$ satisfies:
--
--   1. $\varphi_a$ is twice continuously differentiable;
--   2. $\varphi_a''(x) = V_a'(\varphi_a(x))$ for every $x \in \mathbb R$ (the static field equation);
--   3. $\varphi_a(x) \to -F$ as $x \to -\infty$ and $\varphi_a(x) \to F$ as $x \to +\infty$.
--
--   This confirms that the closed-form kink of Section 1.2 is a static solution interpolating between the two vacua $\pm F$.
-- source:
--   G. 't Hooft, Monopoles, Instantons and Confinement (lecture notes by F. Bruckmann), arXiv:hep-th/0010225, https://arxiv.org/abs/hep-th/0010225, Chapter 1, Section 1.2, pp. 3-4 (solution of (1.6), case (a), and property (i))

import Mathlib
import Definitions.Def_MIC_kink_solitons_1d
open Filter Topology

namespace MonopolesInstantonsConfinement

theorem phi4Kink_isSoliton (lam F x₀ : ℝ) (hlam : 0 < lam) (hF : 0 < F) :
    ContDiff ℝ 2 (phi4Kink lam F x₀) ∧
    (∀ x, deriv (deriv (phi4Kink lam F x₀)) x =
      deriv (phi4Potential lam F) (phi4Kink lam F x₀ x)) ∧
    Tendsto (phi4Kink lam F x₀) atBot (𝓝 (-F)) ∧
    Tendsto (phi4Kink lam F x₀) atTop (𝓝 F) := by sorry

end MonopolesInstantonsConfinement
