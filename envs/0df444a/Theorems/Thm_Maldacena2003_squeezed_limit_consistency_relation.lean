-- Prove2me | Theorems.Thm_Maldacena2003_squeezed_limit_consistency_relation
-- name    : Maldacena2003.squeezed_limit_consistency_relation
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T12:58:03.431472+00:00
-- url     : https://prove2.me/theorems/5dd57ec1-5ab9-4f88-ab9e-ff2320894836
-- title:
--   Maldacena's consistency relation (eqs. 4.5–4.7): $\langle\zeta\zeta\zeta\rangle/(P_\zeta(k_1)P_\zeta(k_3))\to-n_s$ as $k_3\to0$
-- statement:
--   Let $\dot\rho_*>0$, $\dot\phi_*\ne0$, $\ddot\phi_*$ real, and $k>0$. Let $B_\zeta(k_1,k_2,k_3)$ be the leading slow-roll three-scalar correlator of eqs. (4.5)–(4.6), $P_\zeta$ the scalar power spectrum (2.20), and $n_s$ the scalar tilt (2.22). Then, as $(k_2,k_3)\to(k,0)$ through pairs for which $(k,k_2,k_3)$ is a momentum triangle with positive sides,
--   $$\frac{B_\zeta(k,k_2,k_3)}{P_\zeta(k)\,P_\zeta(k_3)} \;\longrightarrow\; -\,n_s .$$
--
--   In words: when one momentum is much smaller than the other two, the three-point function of $\zeta$ equals $-n_s$ times the product of the two-point functions, $\langle\zeta_{\vec k_1}\zeta_{\vec k_2}\zeta_{\vec k_3}\rangle\sim-n_s\langle\zeta_{\vec k_3}\zeta_{-\vec k_3}\rangle'\langle\zeta_{\vec k_1}\zeta_{\vec k_2}\rangle'$. This is the single-field consistency relation, eq. (4.7), recovered from the general formula (4.5)–(4.6).
--
--   **Formalization Note** $M_{pl}=1$, $H_*=\dot\rho_*$, the factor $(2\pi)^3\delta^3(\sum\vec k_i)$ is dropped, and the horizon-crossing times $*$, $*'$ are identified at leading order in slow roll. The limit is taken in $\mathbb R^2$ within the momentum-triangle set; momentum conservation forces $k_2\to k$.
-- source:
--   J. Maldacena, Non-Gaussian features of primordial fluctuations in single field inflationary models, JHEP 05 (2003) 013, https://doi.org/10.1088/1126-6708/2003/05/013 (arXiv:astro-ph/0210603), pp. 16–17, eqs. (4.5)–(4.7); also p. 7, eqs. (2.20), (2.22)

import Mathlib
import Definitions.Def_Maldacena2003_InflationDefs
open Filter Topology

namespace Maldacena2003

theorem squeezed_limit_consistency_relation (ρd φd φdd k : ℝ)
    (hρ : 0 < ρd) (hφ : φd ≠ 0) (hk : 0 < k) :
    Tendsto
      (fun p : ℝ × ℝ => zetaBispectrum ρd φd φdd k p.1 p.2
        / (zetaPowerSpectrum ρd φd k * zetaPowerSpectrum ρd φd p.2))
      (𝓝[{p : ℝ × ℝ | IsMomentumTriangle k p.1 p.2}] (k, 0))
      (𝓝 (-scalarTilt ρd φd φdd)) := by sorry

end Maldacena2003
