-- Prove2me | Theorems.Thm_GoodmanWitten_eq3_photino_rate
-- name    : GoodmanWitten.eq3_photino_rate
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T12:54:57.18999+00:00
-- url     : https://prove2.me/theorems/08736805-1507-44ba-91a3-601cbfc3e8ca
-- title:
--   Eq. (3): event rate for spin-dependent photino scattering
-- statement:
--   Let photinos of mass $m>0$ scatter from nuclei of mass number $A>0$ and mass $M = A\,m_N$ through exchange of a scalar quark of mass $M_{\tilde Q}>0$ whose quark partner has charge $q = Qe$, with $e^2 = 4\pi\alpha$. With spin-averaged squared amplitude $\langle|\mathcal M|^2\rangle = (4q^4/M_{\tilde Q}^4)\,\lambda^2J(J+1)$ and the elastic cross section $\sigma = \frac{m^2M^2}{\pi(m+M)^2}\langle|\mathcal M|^2\rangle$, there is a constant $C$ with $|C/1.1 - 1|\le 0.05$ such that, for all parameters as above and all real $Q$, $\lambda^2J(J+1)$, $\rho$, $v$,
--   $$
--   R = C\left[\frac{100\ \mathrm{GeV}}{M_{\tilde Q}}\right]^4\frac{4mM}{(m+M)^2}\left[\frac{Q}{2/3}\right]^4[\lambda^2J(J+1)]\left[\frac{\rho}{10^{-24}\ \mathrm{g/cm}^3}\right]\left[\frac{v}{200\ \mathrm{km/s}}\right].
--   $$
--
--   This is the paper's rate formula for dark matter with only spin-dependent interactions.
--
--   **Formalization Note** The factor $\lambda^2J(J+1)$ is a free real parameter; 5% relative tolerance on the printed coefficient.
-- source:
--   M. W. Goodman and E. Witten, Detectability of certain dark-matter candidates, Phys. Rev. D 31, 3059-3063 (1985), https://doi.org/10.1103/PhysRevD.31.3059, p. 3061, Eq. (3) and the preceding paragraph

import Mathlib
import Definitions.Def_GoodmanWitten_basic

namespace GoodmanWitten

theorem eq3_photino_rate : ∃ C : ℝ, |C / 1.1 - 1| ≤ 0.05 ∧
    ∀ A m Q MQ lamJJ ρ v : ℝ, 0 < A → 0 < m → 0 < MQ →
      eventRatePerKgDay A (photinoCrossSection m (nucleusMass A) Q MQ lamJJ) ρ v m =
        C * (100 / MQ) ^ 4 * (4 * m * nucleusMass A / (m + nucleusMass A) ^ 2) *
          (Q / (2 / 3)) ^ 4 * lamJJ * (ρ / 1e-24) * (v / 2e7) := by sorry

end GoodmanWitten
