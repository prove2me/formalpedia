-- Prove2me | Theorems.Thm_GoodmanWitten_eq2_coherent_reduced_cross_section
-- name    : GoodmanWitten.eq2_coherent_reduced_cross_section
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T12:53:02.812994+00:00
-- url     : https://prove2.me/theorems/d5071cab-849d-4e97-a3d7-50c318f68d5c
-- title:
--   Eq. (2): reduced cross section for coherent weak scattering
-- statement:
--   Let a halo particle of mass $m>0$ scatter coherently from a nucleus of mass number $A>0$ and mass $M = A\,m_N$ through $Z$ exchange, with amplitude $\mathcal M = G_F\bar Y\bar N/\sqrt2$, so that
--   $$
--   \sigma = \frac{m^2M^2}{2\pi(m+M)^2}\,G_F^2\,\bar Y^2\,\bar N^2
--   $$
--   (converted to cm$^2$). Then there is a constant $C$ with $|C/(2.0\times10^{-35}\ \mathrm{cm}^2) - 1|\le 0.05$ such that for all $A, m > 0$ and all real $\bar Y, \bar N$,
--   $$
--   \bar\sigma = \frac{\sigma}{A}\cdot\frac{1\ \mathrm{GeV}}{m} = C\left[\frac{4mM}{(m+M)^2}\right]\bar Y^2\left[\frac{\bar N}{100}\right]^2 .
--   $$
--
--   Combined with Eq. (1), this gives the event rates for particles with coherent weak interactions (Table II without the form-factor correction).
--
--   **Formalization Note** $M = A\,m_N$ with $m_N = 0.9383$ GeV; 5% relative tolerance on the printed coefficient.
-- source:
--   M. W. Goodman and E. Witten, Detectability of certain dark-matter candidates, Phys. Rev. D 31, 3059-3063 (1985), https://doi.org/10.1103/PhysRevD.31.3059, p. 3060, left column, Eq. (2) and the two preceding sentences

import Mathlib
import Definitions.Def_GoodmanWitten_basic

namespace GoodmanWitten

theorem eq2_coherent_reduced_cross_section : ∃ C : ℝ, |C / 2.0e-35 - 1| ≤ 0.05 ∧
    ∀ A m Ybar Nbar : ℝ, 0 < A → 0 < m →
      reducedCrossSection A (coherentCrossSection m (nucleusMass A) Ybar Nbar) m =
        C * (4 * m * nucleusMass A / (m + nucleusMass A) ^ 2) * Ybar ^ 2 * (Nbar / 100) ^ 2 := by sorry

end GoodmanWitten
