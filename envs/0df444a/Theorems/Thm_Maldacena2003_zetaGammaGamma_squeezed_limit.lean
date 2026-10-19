-- Prove2me | Theorems.Thm_Maldacena2003_zetaGammaGamma_squeezed_limit
-- name    : Maldacena2003.zetaGammaGamma_squeezed_limit
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T12:55:50.471711+00:00
-- url     : https://prove2.me/theorems/7ef78b1d-4d37-4a4a-b845-068b4c4f803f
-- title:
--   Eqs. (4.13) → (4.14): squeezed limit of $\langle\zeta_{\vec k_1}\gamma^{s_2}_{\vec k_2}\gamma^{s_3}_{\vec k_3}\rangle$
-- statement:
--   Let $\dot\rho_*>0$, $\dot\phi_*\ne0$, $k>0$, and let $E$ be real (the polarization contraction $\epsilon^{s_2}_{ij}\epsilon^{s_3}_{ij}$). As $(k_1,k_3)\to(0,k)$ through pairs for which $(k_1,k,k_3)$ is a momentum triangle with positive sides,
--   $$\frac{B_{\zeta\gamma\gamma}(k_1,k,k_3;E)}{P_\zeta(k_1)\,P_\gamma(k)} \;\longrightarrow\; -\frac{E}{2}\,n_t ,$$
--   where $B_{\zeta\gamma\gamma}$ is the correlator (4.13), $P_\zeta$ and $P_\gamma$ are the power spectra (2.20) and (2.29), and $n_t$ is the tensor tilt (2.30).
--
--   For equal polarizations, $\epsilon^{s}_{ij}\epsilon^{s}_{ij} = 2$, and this reads $\langle\zeta\gamma\gamma\rangle\sim -n_t\langle\zeta\zeta\rangle'\langle\gamma\gamma\rangle'$. This is the agreement of (4.13) with (4.14).
--
--   **Formalization Note** $M_{pl}=1$, and the horizon-crossing times $*$, $*'$ are identified at leading order. The polarization contraction enters as the parameter $E$.
-- source:
--   J. Maldacena, Non-Gaussian features of primordial fluctuations in single field inflationary models, JHEP 05 (2003) 013, https://doi.org/10.1088/1126-6708/2003/05/013 (arXiv:astro-ph/0210603), p. 19, eqs. (4.13), (4.14)

import Mathlib
import Definitions.Def_Maldacena2003_InflationDefs
open Filter Topology

namespace Maldacena2003

theorem zetaGammaGamma_squeezed_limit (ρd φd k E : ℝ) (hρ : 0 < ρd) (hφ : φd ≠ 0)
    (hk : 0 < k) :
    Tendsto
      (fun p : ℝ × ℝ => zetaGammaGammaBispectrum ρd p.1 k p.2 E
        / (zetaPowerSpectrum ρd φd p.1 * tensorPowerSpectrum ρd k))
      (𝓝[{p : ℝ × ℝ | IsMomentumTriangle p.1 k p.2}] (0, k))
      (𝓝 (-(E / 2) * tensorTilt ρd φd)) := by sorry

end Maldacena2003
