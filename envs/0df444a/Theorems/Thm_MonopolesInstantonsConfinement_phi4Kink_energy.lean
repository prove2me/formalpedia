-- Prove2me | Theorems.Thm_MonopolesInstantonsConfinement_phi4Kink_energy
-- name    : MonopolesInstantonsConfinement.phi4Kink_energy
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:22:02.056123+00:00
-- url     : https://prove2.me/theorems/f5ff9fbb-5610-4e4a-963e-dcf1777d92c8
-- title:
--   Mass of the $\varphi^4$ kink: $E = 2m^3/\lambda$
-- statement:
--   Let $\lambda > 0$, $F > 0$, $x_0 \in \mathbb R$, $m = \sqrt{\lambda F^2/3}$, and let $\varphi_a(x) = F\tanh\big(\tfrac12 m(x-x_0)\big)$ be the kink of the Mexican-hat potential $V_a(\varphi) = \frac{\lambda}{24}(\varphi^2 - F^2)^2$. Its energy (1.5) is finite and equals
--   $$E_{V_a}[\varphi_a] = \int_{-\infty}^{\infty}\Big(\tfrac12\varphi_a'(x)^2 + V_a(\varphi_a(x))\Big)dx = \frac{2m^3}{\lambda}.$$
--
--   This is the mass of the soliton in case (a); it scales as $m^3/\lambda$ and is therefore large in the weak-coupling regime.
-- source:
--   G. 't Hooft, Monopoles, Instantons and Confinement (lecture notes by F. Bruckmann), arXiv:hep-th/0010225, https://arxiv.org/abs/hep-th/0010225, Chapter 1, Section 1.2, p. 5 (energy of the solution, case (a))

import Mathlib
import Definitions.Def_MIC_kink_solitons_1d
open Filter Topology

namespace MonopolesInstantonsConfinement

theorem phi4Kink_energy (lam F x₀ : ℝ) (hlam : 0 < lam) (hF : 0 < F) :
    staticEnergy (phi4Potential lam F) (phi4Kink lam F x₀) =
      ENNReal.ofReal (2 * phi4Mass lam F ^ 3 / lam) := by sorry

end MonopolesInstantonsConfinement
