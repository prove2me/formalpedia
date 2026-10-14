-- Prove2me | Theorems.Thm_MDOUnifiedCosmology_late_time_density_pressure
-- name    : MDOUnifiedCosmology.late_time_density_pressure
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T13:34:07.517978+00:00
-- url     : https://prove2.me/theorems/c34da1a7-80d8-4623-86b3-1f0fd5b8d0ca
-- title:
--   Late-time MDO energy density and pressure, Eqs. (22)–(23)
-- statement:
--   Throughout, $\kappa^2 = 8\pi G$ (units $c=\hbar=1$), $a(t)>0$ is the scale factor of the flat FLRW metric, $H=\dot a/a$ is the Hubble function, $\phi(t)$ is the time-dependent part of the MDO fermionic field, $V$ is its potential, $\rho_m, p_m$ are the energy density and pressure of the other matter components, and $F(\phi) = 1+\kappa^2\phi^2/8$.
--
--   Let $V=V_1+V_2$ be the potential of Eq. (19), with $A,\phi_c>0$. Suppose that on the half-line $t>T$ the field is frozen at the bottom of the potential, $\phi(t)=\phi_c$, the only other matter is pressureless baryonic matter ($\rho_m=\rho_b$, $p_m=0$), and both Friedmann equations (5) and (6) hold. Then for every $t>T$, with $\rho_\phi$, $p_\phi$ defined by Eqs. (10)–(11),
--
--   $$\rho_\phi=\frac{\kappa^2\phi_c^2}{8}\rho_b+\left(1+\frac{\kappa^2\phi_c^2}{8}\right)V_2(\phi_c),\qquad p_\phi=-\left(1+\frac{\kappa^2\phi_c^2}{8}\right)V_2(\phi_c).$$
--
--   These are Eqs. (22)–(23): a pressureless component tracking the baryons plus a cosmological-constant-like component.
-- source:
--   S. H. Pereira, M. E. S. Alves, T. M. Guimarães, "An unified cosmological evolution driven by a mass dimension one fermionic field", Eur. Phys. J. C 79 (2019) 543, https://doi.org/10.1140/epjc/s10052-019-7036-5, p. 4, Sect. 3, Eqs. (22)–(23)

import Mathlib
import Definitions.Def_MDOUnifiedCosmology_model

open MDOUnifiedCosmology Set

namespace MDOUnifiedCosmology

theorem late_time_density_pressure (κ A φc m α : ℝ) (hA : 0 < A) (hφc : 0 < φc)
    (T : ℝ) (a φ ρb : ℝ → ℝ) (hφ : ∀ t ∈ Ioi T, φ t = φc)
    (h5 : ∀ t ∈ Ioi T, FriedmannEq κ (potential A φc m α) a φ ρb t)
    (h6 : ∀ t ∈ Ioi T, AccelerationEq κ a φ ρb (fun _ => 0) t) :
    ∀ t ∈ Ioi T,
      rhoPhi κ (potential A φc m α) a φ t =
          κ ^ 2 * φc ^ 2 / 8 * ρb t + couplingFactor κ φc * V2 m α φc ∧
      pPhi κ (potential A φc m α) a φ t = -(couplingFactor κ φc * V2 m α φc) := by
  sorry

end MDOUnifiedCosmology
