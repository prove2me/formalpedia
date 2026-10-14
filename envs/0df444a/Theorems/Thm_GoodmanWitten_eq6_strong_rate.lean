-- Prove2me | Theorems.Thm_GoodmanWitten_eq6_strong_rate
-- name    : GoodmanWitten.eq6_strong_rate
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T12:58:18.867108+00:00
-- url     : https://prove2.me/theorems/58f5e432-eed6-4ca6-8cb4-8be2c2b4f7f5
-- title:
--   Eq. (6): counting rate for strongly interacting particles
-- statement:
--   Let strongly interacting particles of mass $M_X>0$ (GeV) scatter from nuclei of mass number $A>0$ with the hard-sphere cross section $\sigma = 4\pi(1.25A^{1/3}\times10^{-13}\ \mathrm{cm})^2$, and let $\epsilon$ be the stopping factor of the earth or atmosphere. Then there is a constant $C$ with $|C/(1.15\times10^{14}) - 1|\le0.05$ such that for all $A, M_X>0$ and all real $\epsilon,\rho,v$ the rate $R = \epsilon\,KF\sigma$ satisfies
--   $$
--   R = C\,A^{-1/3}\,\epsilon\left[\frac{1\ \mathrm{GeV}}{M_X}\right]\left[\frac{\rho}{10^{-24}\ \mathrm{g/cm}^3}\right]\left[\frac{v}{200\ \mathrm{km/s}}\right].
--   $$
--
--   **Formalization Note** $\epsilon$ is a free parameter multiplying the rate; 5% relative tolerance on the printed coefficient.
-- source:
--   M. W. Goodman and E. Witten, Detectability of certain dark-matter candidates, Phys. Rev. D 31, 3059-3063 (1985), https://doi.org/10.1103/PhysRevD.31.3059, p. 3062, right column, Eq. (6)

import Mathlib
import Definitions.Def_GoodmanWitten_basic

namespace GoodmanWitten

theorem eq6_strong_rate : ∃ C : ℝ, |C / 1.15e14 - 1| ≤ 0.05 ∧
    ∀ A MX ε ρ v : ℝ, 0 < A → 0 < MX →
      strongEventRate A MX ε ρ v =
        C * A ^ (-(1 : ℝ) / 3) * ε * (1 / MX) * (ρ / 1e-24) * (v / 2e7) := by sorry

end GoodmanWitten
