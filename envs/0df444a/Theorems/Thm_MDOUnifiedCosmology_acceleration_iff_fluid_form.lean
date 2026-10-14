-- Prove2me | Theorems.Thm_MDOUnifiedCosmology_acceleration_iff_fluid_form
-- name    : MDOUnifiedCosmology.acceleration_iff_fluid_form
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T13:30:22.171986+00:00
-- url     : https://prove2.me/theorems/74e7a896-fbe4-464b-bdcd-0b7edb855373
-- title:
--   Eq. (6) is equivalent to the perfect-fluid acceleration equation (16)
-- statement:
--   Throughout, $\kappa^2 = 8\pi G$ (units $c=\hbar=1$), $a(t)>0$ is the scale factor of the flat FLRW metric, $H=\dot a/a$ is the Hubble function, $\phi(t)$ is the time-dependent part of the MDO fermionic field, $V$ is its potential, $\rho_m, p_m$ are the energy density and pressure of the other matter components, and $F(\phi) = 1+\kappa^2\phi^2/8$.
--
--   With $\rho_\phi$, $p_\phi$ defined by Eqs. (10)–(11), at every time $t$ the second Friedmann equation (6),
--
--   $$\dot H=-\frac{\kappa^2}{2}\left(1+\frac{\kappa^2\phi^2}{8}\right)\left[\dot\phi^2-\frac12\frac{H\phi\dot\phi}{(1+\kappa^2\phi^2/8)^2}+\rho_m+p_m\right],$$
--
--   holds if and only if the perfect-fluid form (16) holds:
--
--   $$\dot H=-\frac{\kappa^2}{2}(\rho_\phi+p_\phi+\rho_m+p_m).$$
-- source:
--   S. H. Pereira, M. E. S. Alves, T. M. Guimarães, "An unified cosmological evolution driven by a mass dimension one fermionic field", Eur. Phys. J. C 79 (2019) 543, https://doi.org/10.1140/epjc/s10052-019-7036-5, p. 3, Eqs. (6), (10), (11), (16)

import Mathlib
import Definitions.Def_MDOUnifiedCosmology_model

open MDOUnifiedCosmology Set

namespace MDOUnifiedCosmology

theorem acceleration_iff_fluid_form (κ : ℝ) (V : ℝ → ℝ) (a φ ρm pm : ℝ → ℝ) (t : ℝ) :
    AccelerationEq κ a φ ρm pm t ↔
      deriv (hubble a) t =
        -(κ ^ 2 / 2) * (rhoPhi κ V a φ t + pPhi κ V a φ t + ρm t + pm t) := by
  sorry

end MDOUnifiedCosmology
