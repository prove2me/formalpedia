-- Prove2me | Theorems.Thm_MDOUnifiedCosmology_dust_density_scaling
-- name    : MDOUnifiedCosmology.dust_density_scaling
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T13:33:39.387231+00:00
-- url     : https://prove2.me/theorems/bdabe7bf-38b1-4384-9fc0-f93eda12a663
-- title:
--   Pressureless matter dilutes as $a^{-3}$ (Eq. (9) with $p_m = 0$)
-- statement:
--   Let $a$ be a positive, differentiable scale factor on the half-line $t>T$ with Hubble function $H=\dot a/a$, and let $\rho_b$ be a differentiable energy density of pressureless matter obeying the conservation equation (9) with $p_m=0$:
--
--   $$\dot\rho_b+3H\rho_b=0\quad(t>T).$$
--
--   Then $\rho_b a^3$ is constant: for any $t,t_0>T$,
--
--   $$\rho_b(t)\,a(t)^3=\rho_b(t_0)\,a(t_0)^3.$$
--
--   This is the $a^{-3}$ dilution of baryonic matter used in Sect. 3 to obtain the $\Omega_b/a^3$ and $\Omega_{DM,\phi}/a^3$ terms of Eq. (25).
-- source:
--   S. H. Pereira, M. E. S. Alves, T. M. Guimarães, "An unified cosmological evolution driven by a mass dimension one fermionic field", Eur. Phys. J. C 79 (2019) 543, https://doi.org/10.1140/epjc/s10052-019-7036-5, p. 3 Eq. (9) and p. 4, Sect. 3 ($\rho_m=\rho_b$, $p_m=p_b=0$), used in Eq. (25)

import Mathlib
import Definitions.Def_MDOUnifiedCosmology_model

open MDOUnifiedCosmology Set

namespace MDOUnifiedCosmology

theorem dust_density_scaling (T t₀ : ℝ) (ht₀ : T < t₀) (a ρb : ℝ → ℝ)
    (ha_pos : ∀ t ∈ Ioi T, 0 < a t) (ha_diff : DifferentiableOn ℝ a (Ioi T))
    (hρb_diff : DifferentiableOn ℝ ρb (Ioi T))
    (hcons : ∀ t ∈ Ioi T, MatterConservation a ρb (fun _ => 0) t) :
    ∀ t ∈ Ioi T, ρb t * a t ^ 3 = ρb t₀ * a t₀ ^ 3 := by
  sorry

end MDOUnifiedCosmology
