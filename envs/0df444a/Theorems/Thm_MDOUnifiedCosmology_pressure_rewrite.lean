-- Prove2me | Theorems.Thm_MDOUnifiedCosmology_pressure_rewrite
-- name    : MDOUnifiedCosmology.pressure_rewrite
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T13:28:05.54899+00:00
-- url     : https://prove2.me/theorems/95fa1491-cef9-49d3-8f19-7c1bc75d5af4
-- title:
--   MDO pressure in terms of matter pressure, Eq. (13)
-- statement:
--   Throughout, $\kappa^2 = 8\pi G$ (units $c=\hbar=1$), $a(t)>0$ is the scale factor of the flat FLRW metric, $H=\dot a/a$ is the Hubble function, $\phi(t)$ is the time-dependent part of the MDO fermionic field, $V$ is its potential, $\rho_m, p_m$ are the energy density and pressure of the other matter components, and $F(\phi) = 1+\kappa^2\phi^2/8$.
--
--   Let the MDO pressure be defined by Eq. (11),
--   $p_\phi=\frac{\dot\phi^2}{2}-V(\phi)-\frac38\frac{H^2\phi^2}{1+\kappa^2\phi^2/8}-\frac14\frac{\dot H\phi^2}{1+\kappa^2\phi^2/8}-\frac12\frac{H\phi\dot\phi}{(1+\kappa^2\phi^2/8)^2}$.
--   If at time $t$ both Friedmann equations (5) and (6) hold, then
--
--   $$p_\phi=\frac{\kappa^2\phi^2}{8}p_m+\left(1+\frac{\kappa^2\phi^2}{8}\right)\left[\frac{\dot\phi^2}{2}-V(\phi)\right]-\frac12\frac{H\phi\dot\phi}{1+\kappa^2\phi^2/8}.$$
--
--   This is Eq. (13), the pressure counterpart of Eq. (12).
-- source:
--   S. H. Pereira, M. E. S. Alves, T. M. Guimarães, "An unified cosmological evolution driven by a mass dimension one fermionic field", Eur. Phys. J. C 79 (2019) 543, https://doi.org/10.1140/epjc/s10052-019-7036-5, p. 3, Eqs. (5), (6), (11), (13)

import Mathlib
import Definitions.Def_MDOUnifiedCosmology_model

open MDOUnifiedCosmology Set

namespace MDOUnifiedCosmology

theorem pressure_rewrite (κ : ℝ) (V : ℝ → ℝ) (a φ ρm pm : ℝ → ℝ) (t : ℝ)
    (h5 : FriedmannEq κ V a φ ρm t) (h6 : AccelerationEq κ a φ ρm pm t) :
    pPhi κ V a φ t = κ ^ 2 * φ t ^ 2 / 8 * pm t
      + couplingFactor κ (φ t) * (deriv φ t ^ 2 / 2 - V (φ t))
      - 1 / 2 * (hubble a t * φ t * deriv φ t / couplingFactor κ (φ t)) := by
  sorry

end MDOUnifiedCosmology
