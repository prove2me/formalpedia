-- Prove2me | Theorems.Thm_MonopolesInstantonsConfinement_sineGordon_bogomolnyi_bound
-- name    : MonopolesInstantonsConfinement.sineGordon_bogomolnyi_bound
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:23:46.647981+00:00
-- url     : https://prove2.me/theorems/912ec2be-dfb5-4ea5-a01c-d84bd25b0607
-- title:
--   Bogomol'nyi bound for the sine-Gordon model
-- statement:
--   Let $A > 0$, $F > 0$, $m = 2\pi\sqrt A/F$, $\lambda = 16\pi^4 A/F^4$, and let $V_b(\varphi) = A\big(1 - \cos\frac{2\pi\varphi}{F}\big)$. For every differentiable $\varphi : \mathbb R \to \mathbb R$ with
--   $$\lim_{x\to-\infty}\varphi(x) = 0, \qquad \lim_{x\to+\infty}\varphi(x) = F,$$
--   the energy satisfies
--   $$E_{V_b}[\varphi] = \int_{-\infty}^{\infty}\Big(\tfrac12\varphi'(x)^2 + V_b(\varphi(x))\Big)dx \ \ge\ \frac{8m^3}{\lambda}$$
--   (the energy may be $+\infty$).
--
--   This is the Bogomol'nyi bound of Exercise (i) for case (b), in the sector joining the neighbouring vacua $0$ and $F$.
-- source:
--   G. 't Hooft, Monopoles, Instantons and Confinement (lecture notes by F. Bruckmann), arXiv:hep-th/0010225, https://arxiv.org/abs/hep-th/0010225, Chapter 1, Section 1.2, p. 5, eq. (1.7), and Chapter 7, Exercise (i), p. 66

import Mathlib
import Definitions.Def_MIC_kink_solitons_1d
open Filter Topology

namespace MonopolesInstantonsConfinement

theorem sineGordon_bogomolnyi_bound (A F : ℝ) (hA : 0 < A) (hF : 0 < F)
    (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ)
    (hbot : Tendsto φ atBot (𝓝 0)) (htop : Tendsto φ atTop (𝓝 F)) :
    ENNReal.ofReal (8 * sineGordonMass A F ^ 3 / sineGordonCoupling A F) ≤
      staticEnergy (sineGordonPotential A F) φ := by sorry

end MonopolesInstantonsConfinement
