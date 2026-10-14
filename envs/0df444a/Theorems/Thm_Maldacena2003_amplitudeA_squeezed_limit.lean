-- Prove2me | Theorems.Thm_Maldacena2003_amplitudeA_squeezed_limit
-- name    : Maldacena2003.amplitudeA_squeezed_limit
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T12:52:28.650935+00:00
-- url     : https://prove2.me/theorems/a2dad588-ebe1-4fe5-a41c-a4fbae30dfa3
-- title:
--   Eq. (4.6) → (4.7): squeezed limit $\mathcal A(k,k_2,k_3)\to -2k^3 n_s$
-- statement:
--   Let $k>0$ and let $\dot\rho_*,\dot\phi_*,\ddot\phi_*$ be real numbers. As $(k_2,k_3)\to(k,0)$ through pairs for which $(k,k_2,k_3)$ is a momentum triangle with positive sides, the amplitude $\mathcal A$ of eq. (4.6) satisfies
--   $$\mathcal A(k,k_2,k_3)\;\longrightarrow\; -2k^3\,n_s = 4k^3\Big(\frac{\ddot\phi_*}{\dot\phi_*\dot\rho_*}+\frac{\dot\phi_*^2}{\dot\rho_*^2}\Big).$$
--
--   This is the step at which the general slow-roll result (4.6) reproduces the squeezed-limit form (4.7) of the three-scalar correlator.
--
--   **Formalization Note** The limit is taken in $\mathbb R^2$ within the set $\{(k_2,k_3) : \texttt{IsMomentumTriangle}\ k\ k_2\ k_3\}$, whose closure contains $(k,0)$.
-- source:
--   J. Maldacena, Non-Gaussian features of primordial fluctuations in single field inflationary models, JHEP 05 (2003) 013, https://doi.org/10.1088/1126-6708/2003/05/013 (arXiv:astro-ph/0210603), pp. 16–17, eqs. (4.6), (4.7)

import Mathlib
import Definitions.Def_Maldacena2003_InflationDefs
open Filter Topology

namespace Maldacena2003

theorem amplitudeA_squeezed_limit (ρd φd φdd k : ℝ) (hk : 0 < k) :
    Tendsto (fun p : ℝ × ℝ => amplitudeA ρd φd φdd k p.1 p.2)
      (𝓝[{p : ℝ × ℝ | IsMomentumTriangle k p.1 p.2}] (k, 0))
      (𝓝 (-(2 * k ^ 3) * scalarTilt ρd φd φdd)) := by sorry

end Maldacena2003
