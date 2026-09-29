-- Prove2me | Theorems.Thm_MonopolesInstantonsConfinement_sineGordonKink_energy
-- name    : MonopolesInstantonsConfinement.sineGordonKink_energy
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:22:22.165713+00:00
-- url     : https://prove2.me/theorems/bd24e90d-041b-4022-8411-09fa45d95d20
-- title:
--   Mass of the sine-Gordon soliton: $E = 8m^3/\lambda$
-- statement:
--   Let $A > 0$, $F > 0$, $x_0 \in \mathbb R$, $m = 2\pi\sqrt A/F$ and $\lambda = 16\pi^4 A/F^4$, and let $\varphi_b(x) = \frac{2F}{\pi}\arctan\big(e^{m(x-x_0)}\big)$ be the soliton of the sine-Gordon potential $V_b(\varphi) = A\big(1 - \cos\frac{2\pi\varphi}{F}\big)$. Its energy (1.5) is finite and equals
--   $$E_{V_b}[\varphi_b] = \int_{-\infty}^{\infty}\Big(\tfrac12\varphi_b'(x)^2 + V_b(\varphi_b(x))\Big)dx = \frac{8m^3}{\lambda}.$$
--
--   This is the mass of the soliton in case (b), again of order $m^3/\lambda$.
-- source:
--   G. 't Hooft, Monopoles, Instantons and Confinement (lecture notes by F. Bruckmann), arXiv:hep-th/0010225, https://arxiv.org/abs/hep-th/0010225, Chapter 1, Section 1.2, p. 5 (energy of the solution, case (b))

import Mathlib
import Definitions.Def_MIC_kink_solitons_1d
open Filter Topology

namespace MonopolesInstantonsConfinement

theorem sineGordonKink_energy (A F x₀ : ℝ) (hA : 0 < A) (hF : 0 < F) :
    staticEnergy (sineGordonPotential A F) (sineGordonKink A F x₀) =
      ENNReal.ofReal (8 * sineGordonMass A F ^ 3 / sineGordonCoupling A F) := by sorry

end MonopolesInstantonsConfinement
