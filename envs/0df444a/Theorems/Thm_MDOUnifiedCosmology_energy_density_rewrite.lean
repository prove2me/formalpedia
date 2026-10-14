-- Prove2me | Theorems.Thm_MDOUnifiedCosmology_energy_density_rewrite
-- name    : MDOUnifiedCosmology.energy_density_rewrite
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T13:27:31.154117+00:00
-- url     : https://prove2.me/theorems/a777245f-5133-4665-8b58-7b55dbd30aa8
-- title:
--   MDO energy density in terms of matter density, Eq. (12)
-- statement:
--   Throughout, $\kappa^2 = 8\pi G$ (units $c=\hbar=1$), $a(t)>0$ is the scale factor of the flat FLRW metric, $H=\dot a/a$ is the Hubble function, $\phi(t)$ is the time-dependent part of the MDO fermionic field, $V$ is its potential, $\rho_m, p_m$ are the energy density and pressure of the other matter components, and $F(\phi) = 1+\kappa^2\phi^2/8$.
--
--   Let the MDO energy density be defined by Eq. (10),
--   $\rho_\phi=\frac{\dot\phi^2}{2}+V(\phi)+\frac38\frac{H^2\phi^2}{1+\kappa^2\phi^2/8}$.
--   If at time $t$ the first Friedmann equation (5) holds, then
--
--   $$\rho_\phi=\frac{\kappa^2\phi^2}{8}\rho_m+\left(1+\frac{\kappa^2\phi^2}{8}\right)\left[\frac{\dot\phi^2}{2}+V(\phi)\right].$$
--
--   This is Eq. (12); the first term exhibits the coupling between the MDO field and the matter density that is responsible for the dark matter behaviour.
-- source:
--   S. H. Pereira, M. E. S. Alves, T. M. Guimarães, "An unified cosmological evolution driven by a mass dimension one fermionic field", Eur. Phys. J. C 79 (2019) 543, https://doi.org/10.1140/epjc/s10052-019-7036-5, p. 3, Eqs. (5), (10), (12)

import Mathlib
import Definitions.Def_MDOUnifiedCosmology_model

open MDOUnifiedCosmology Set

namespace MDOUnifiedCosmology

theorem energy_density_rewrite (κ : ℝ) (V : ℝ → ℝ) (a φ ρm : ℝ → ℝ) (t : ℝ)
    (h5 : FriedmannEq κ V a φ ρm t) :
    rhoPhi κ V a φ t = κ ^ 2 * φ t ^ 2 / 8 * ρm t
      + couplingFactor κ (φ t) * (deriv φ t ^ 2 / 2 + V (φ t)) := by
  sorry

end MDOUnifiedCosmology
