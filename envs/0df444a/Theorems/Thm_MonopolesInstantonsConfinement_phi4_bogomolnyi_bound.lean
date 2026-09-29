-- Prove2me | Theorems.Thm_MonopolesInstantonsConfinement_phi4_bogomolnyi_bound
-- name    : MonopolesInstantonsConfinement.phi4_bogomolnyi_bound
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:22:52.914619+00:00
-- url     : https://prove2.me/theorems/f901c7ad-9bef-4190-9873-06daeea95134
-- title:
--   Bogomol'nyi bound for the $\varphi^4$ model
-- statement:
--   Let $\lambda > 0$, $F > 0$ and $m = \sqrt{\lambda F^2/3}$, and let $V_a(\varphi) = \frac{\lambda}{24}(\varphi^2 - F^2)^2$. For every differentiable $\varphi : \mathbb R \to \mathbb R$ with
--   $$\lim_{x\to-\infty}\varphi(x) = -F, \qquad \lim_{x\to+\infty}\varphi(x) = F,$$
--   the energy satisfies
--   $$E_{V_a}[\varphi] = \int_{-\infty}^{\infty}\Big(\tfrac12\varphi'(x)^2 + V_a(\varphi(x))\Big)dx \ \ge\ \frac{2m^3}{\lambda}$$
--   (the energy may be $+\infty$).
--
--   This is the Bogomol'nyi bound of Exercise (i): the energy in the one-kink sector is bounded below by the boundary term $W(F) - W(-F)$, where $W' = \sqrt{2V_a}$.
-- source:
--   G. 't Hooft, Monopoles, Instantons and Confinement (lecture notes by F. Bruckmann), arXiv:hep-th/0010225, https://arxiv.org/abs/hep-th/0010225, Chapter 1, Section 1.2, p. 5, eq. (1.7), and Chapter 7, Exercise (i), p. 66

import Mathlib
import Definitions.Def_MIC_kink_solitons_1d
open Filter Topology

namespace MonopolesInstantonsConfinement

theorem phi4_bogomolnyi_bound (lam F : ℝ) (hlam : 0 < lam) (hF : 0 < F)
    (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ)
    (hbot : Tendsto φ atBot (𝓝 (-F))) (htop : Tendsto φ atTop (𝓝 F)) :
    ENNReal.ofReal (2 * phi4Mass lam F ^ 3 / lam) ≤ staticEnergy (phi4Potential lam F) φ := by sorry

end MonopolesInstantonsConfinement
