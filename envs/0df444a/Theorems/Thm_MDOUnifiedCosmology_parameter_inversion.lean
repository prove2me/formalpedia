-- Prove2me | Theorems.Thm_MDOUnifiedCosmology_parameter_inversion
-- name    : MDOUnifiedCosmology.parameter_inversion
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T13:34:27.900976+00:00
-- url     : https://prove2.me/theorems/76764c97-52df-4e90-b6a0-fb361dea64ab
-- title:
--   Inverting the density parameters for $\phi_c$ and $V_2(\phi_c)$, Eqs. (26)–(27)
-- statement:
--   Let $m_{pl}>0$ be the Planck mass with $\kappa^2=8\pi/m_{pl}^2$, let $H_0\neq0$, $\rho_{b,0}>0$, $\phi_c>0$, and use the density parameters $\rho_{\mathrm{crit},0}=3H_0^2/\kappa^2$, $\Omega_b=\rho_{b,0}/\rho_{\mathrm{crit},0}$, $\Omega_{DM,\phi}=\frac{\kappa^2\phi_c^2}{8}\Omega_b$ (Eq. (26)), $\Lambda_{\mathrm{eff}}=\kappa^2\left(1+\frac{\kappa^2\phi_c^2}{8}\right)V_2(\phi_c)$ (Eq. (24)) and $\Omega_{\Lambda,\phi}=\Lambda_{\mathrm{eff}}/(\kappa^2\rho_{\mathrm{crit},0})$. Then
--
--   1. $\displaystyle \phi_c=m_{pl}\sqrt{\frac{\Omega_{DM,\phi}}{\pi\,\Omega_b}}$ (Sect. 6), and
--   2. $\displaystyle V_2(\phi_c)=\left(\frac{\Omega_{\Lambda,\phi}}{1+\Omega_{DM,\phi}/\Omega_b}\right)\rho_{\mathrm{crit},0}$ (Eq. (27)).
--
--   These formulas express the model parameters through observable density parameters.
-- source:
--   S. H. Pereira, M. E. S. Alves, T. M. Guimarães, "An unified cosmological evolution driven by a mass dimension one fermionic field", Eur. Phys. J. C 79 (2019) 543, https://doi.org/10.1140/epjc/s10052-019-7036-5, p. 5, Eq. (27) and the sentence before it; p. 8, Sect. 6 ($\phi_c = m_{pl}\sqrt{\Omega_{DM,\phi}/\pi\Omega_b}$); $\kappa^2 = 8\pi/m_{pl}^2$ from p. 2 below Eq. (1)

import Mathlib
import Definitions.Def_MDOUnifiedCosmology_model

open MDOUnifiedCosmology Set

namespace MDOUnifiedCosmology

theorem parameter_inversion (κ mpl H₀ ρb₀ φc m α : ℝ) (hmpl : 0 < mpl)
    (hκ : κ ^ 2 = 8 * Real.pi / mpl ^ 2) (hH₀ : H₀ ≠ 0) (hρb₀ : 0 < ρb₀) (hφc : 0 < φc) :
    φc = mpl * Real.sqrt (omegaDM κ φc (omegaB κ H₀ ρb₀) / (Real.pi * omegaB κ H₀ ρb₀)) ∧
    V2 m α φc = omegaLambda κ H₀ φc m α /
        (1 + omegaDM κ φc (omegaB κ H₀ ρb₀) / omegaB κ H₀ ρb₀) * critDensity κ H₀ := by
  sorry

end MDOUnifiedCosmology
