-- Prove2me | Theorems.Thm_MDOUnifiedCosmology_late_time_LCDM
-- name    : MDOUnifiedCosmology.late_time_LCDM
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T13:37:18.813693+00:00
-- url     : https://prove2.me/theorems/6bef2f69-a046-446a-864c-c85b2db00879
-- title:
--   Late-time MDO cosmology has exactly the ΛCDM Hubble function (Eqs. (22)–(26))
-- statement:
--   **Late-time MDO cosmology reproduces the $\Lambda$CDM expansion law.**
--
--   Consider the model with potential $V=V_1+V_2$, $V_1(\phi)=A^4(1-\phi^2/\phi_c^2)^2$, $V_2(\phi)=\tfrac12 m^2\phi^2+\tfrac\alpha4\phi^4$, where $\kappa, A,\phi_c>0$. Suppose that on a late-time interval $t>T$:
--
--   1. the scale factor $a$ is positive and differentiable, and the baryon density $\rho_b$ is differentiable;
--   2. the MDO field sits at the bottom of the symmetry-breaking potential, $\phi(t)=\phi_c$;
--   3. the only other matter is pressureless baryonic matter: $\dot\rho_b+3H\rho_b=0$ (Eq. (9) with $\rho_m=\rho_b$, $p_m=0$);
--   4. the first Friedmann equation (5) holds, $H^2=\frac{\kappa^2}{3}\left(1+\frac{\kappa^2\phi^2}{8}\right)\left[\frac{\dot\phi^2}{2}+V(\phi)+\rho_b\right]$.
--
--   Fix a reference time $t_0>T$ with $a(t_0)=1$ and $H_0=H(t_0)\neq0$. Set $\rho_{\mathrm{crit},0}=3H_0^2/\kappa^2$, $\Omega_b=\rho_b(t_0)/\rho_{\mathrm{crit},0}$, $\Omega_{DM,\phi}=\frac{\kappa^2\phi_c^2}{8}\Omega_b$, $\Lambda_{\mathrm{eff}}=\kappa^2\left(1+\frac{\kappa^2\phi_c^2}{8}\right)V_2(\phi_c)$ and $\Omega_{\Lambda,\phi}=\Lambda_{\mathrm{eff}}/(\kappa^2\rho_{\mathrm{crit},0})$. Then for every $t>T$
--
--   $$\frac{H(t)^2}{H_0^2}=\frac{\Omega_b}{a(t)^3}+\frac{\Omega_{DM,\phi}}{a(t)^3}+\Omega_{\Lambda,\phi}.$$
--
--   This is Eq. (25) of the paper: once the field is frozen at $\phi_c$, its gravitational (spinorial) coupling to baryons acts as a dark matter component scaling like $a^{-3}$, and the residual potential energy $V_2(\phi_c)$ acts as a cosmological constant.
--
--   **Formalization Note** The frozen-field regime is encoded exactly ($\phi\equiv\phi_c$, hence $\dot\phi=0$ and $V_1(\phi_c)=0$); the field equation (7) is deliberately not assumed, since the paper uses only Eqs. (12)/(15) in this regime. The hypotheses are stated on the open half-line $(T,\infty)$ rather than on all of $\mathbb R$, because a matter-filled expanding universe cannot have $a>0$ for all times. The positivity of $A$ is the paper's standing assumption.
-- source:
--   S. H. Pereira, M. E. S. Alves, T. M. Guimarães, "An unified cosmological evolution driven by a mass dimension one fermionic field", Eur. Phys. J. C 79 (2019) 543, https://doi.org/10.1140/epjc/s10052-019-7036-5, p. 4, Sect. 3, Eqs. (22)–(26) with footnote 2

import Mathlib
import Definitions.Def_MDOUnifiedCosmology_model

open MDOUnifiedCosmology Set

namespace MDOUnifiedCosmology

theorem late_time_LCDM (κ A φc m α : ℝ) (hκ : 0 < κ) (hA : 0 < A) (hφc : 0 < φc)
    (T t₀ : ℝ) (ht₀ : T < t₀) (a φ ρb : ℝ → ℝ)
    (ha_pos : ∀ t ∈ Ioi T, 0 < a t) (ha_diff : DifferentiableOn ℝ a (Ioi T))
    (hρb_diff : DifferentiableOn ℝ ρb (Ioi T))
    (hφ : ∀ t ∈ Ioi T, φ t = φc)
    (ha₀ : a t₀ = 1) (hH₀ : hubble a t₀ ≠ 0)
    (hcons : ∀ t ∈ Ioi T, MatterConservation a ρb (fun _ => 0) t)
    (hfried : ∀ t ∈ Ioi T, FriedmannEq κ (potential A φc m α) a φ ρb t) :
    ∀ t ∈ Ioi T,
      hubble a t ^ 2 / hubble a t₀ ^ 2 =
        omegaB κ (hubble a t₀) (ρb t₀) / a t ^ 3
          + omegaDM κ φc (omegaB κ (hubble a t₀) (ρb t₀)) / a t ^ 3
          + omegaLambda κ (hubble a t₀) φc m α := by
  sorry

end MDOUnifiedCosmology
