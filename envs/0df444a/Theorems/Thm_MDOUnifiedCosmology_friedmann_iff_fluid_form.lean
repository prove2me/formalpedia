-- Prove2me | Theorems.Thm_MDOUnifiedCosmology_friedmann_iff_fluid_form
-- name    : MDOUnifiedCosmology.friedmann_iff_fluid_form
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T13:29:47.793421+00:00
-- url     : https://prove2.me/theorems/a13317ab-1b3e-4912-bdc6-197f9eedea5b
-- title:
--   Eq. (5) is equivalent to the perfect-fluid Friedmann equation (15)
-- statement:
--   Throughout, $\kappa^2 = 8\pi G$ (units $c=\hbar=1$), $a(t)>0$ is the scale factor of the flat FLRW metric, $H=\dot a/a$ is the Hubble function, $\phi(t)$ is the time-dependent part of the MDO fermionic field, $V$ is its potential, $\rho_m, p_m$ are the energy density and pressure of the other matter components, and $F(\phi) = 1+\kappa^2\phi^2/8$.
--
--   With $\rho_\phi$ defined by Eq. (10), at every time $t$ the first Friedmann equation (5),
--
--   $$H^2=\frac{\kappa^2}{3}\left(1+\frac{\kappa^2\phi^2}{8}\right)\left[\frac{\dot\phi^2}{2}+V(\phi)+\rho_m\right],$$
--
--   holds if and only if the perfect-fluid form (15) holds:
--
--   $$H^2=\frac{\kappa^2}{3}(\rho_\phi+\rho_m).$$
--
--   This shows that the torsionful MDO model is equivalent in form to a torsion-free model with two perfect fluids.
-- source:
--   S. H. Pereira, M. E. S. Alves, T. M. Guimarães, "An unified cosmological evolution driven by a mass dimension one fermionic field", Eur. Phys. J. C 79 (2019) 543, https://doi.org/10.1140/epjc/s10052-019-7036-5, p. 3, Eqs. (5), (10), (15)

import Mathlib
import Definitions.Def_MDOUnifiedCosmology_model

open MDOUnifiedCosmology Set

namespace MDOUnifiedCosmology

theorem friedmann_iff_fluid_form (κ : ℝ) (V : ℝ → ℝ) (a φ ρm : ℝ → ℝ) (t : ℝ) :
    FriedmannEq κ V a φ ρm t ↔
      hubble a t ^ 2 = κ ^ 2 / 3 * (rhoPhi κ V a φ t + ρm t) := by
  sorry

end MDOUnifiedCosmology
