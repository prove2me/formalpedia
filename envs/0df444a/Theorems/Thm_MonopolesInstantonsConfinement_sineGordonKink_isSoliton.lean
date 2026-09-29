-- Prove2me | Theorems.Thm_MonopolesInstantonsConfinement_sineGordonKink_isSoliton
-- name    : MonopolesInstantonsConfinement.sineGordonKink_isSoliton
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:21:29.572972+00:00
-- url     : https://prove2.me/theorems/180c4e53-2e08-449c-9314-0553f9ac60fc
-- title:
--   The sine-Gordon soliton is a static soliton from $0$ to $F$
-- statement:
--   Let $A > 0$, $F > 0$, $x_0 \in \mathbb R$, and let $m = 2\pi\sqrt A/F$. The sine-Gordon soliton
--   $$\varphi_b(x) = \frac{2F}{\pi}\arctan\big(e^{m(x-x_0)}\big)$$
--   of the potential $V_b(\varphi) = A\big(1 - \cos\frac{2\pi\varphi}{F}\big)$ satisfies:
--
--   1. $\varphi_b$ is twice continuously differentiable;
--   2. $\varphi_b''(x) = V_b'(\varphi_b(x))$ for every $x \in \mathbb R$;
--   3. $\varphi_b(x) \to 0$ as $x \to -\infty$ and $\varphi_b(x) \to F$ as $x \to +\infty$.
--
--   This confirms that the closed-form sine-Gordon soliton interpolates between the neighbouring vacua $0$ and $F$.
-- source:
--   G. 't Hooft, Monopoles, Instantons and Confinement (lecture notes by F. Bruckmann), arXiv:hep-th/0010225, https://arxiv.org/abs/hep-th/0010225, Chapter 1, Section 1.2, pp. 3-4 (solution of (1.6), case (b), and property (i))

import Mathlib
import Definitions.Def_MIC_kink_solitons_1d
open Filter Topology

namespace MonopolesInstantonsConfinement

theorem sineGordonKink_isSoliton (A F x₀ : ℝ) (hA : 0 < A) (hF : 0 < F) :
    ContDiff ℝ 2 (sineGordonKink A F x₀) ∧
    (∀ x, deriv (deriv (sineGordonKink A F x₀)) x =
      deriv (sineGordonPotential A F) (sineGordonKink A F x₀ x)) ∧
    Tendsto (sineGordonKink A F x₀) atBot (𝓝 0) ∧
    Tendsto (sineGordonKink A F x₀) atTop (𝓝 F) := by sorry

end MonopolesInstantonsConfinement
