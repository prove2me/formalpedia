-- Prove2me | Theorems.Thm_MDOUnifiedCosmology_conservation_iff_field_eq
-- name    : MDOUnifiedCosmology.conservation_iff_field_eq
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T13:31:12.022034+00:00
-- url     : https://prove2.me/theorems/d2f4fbe9-3be1-405f-9527-c9b6ecc797a6
-- title:
--   MDO fluid conservation (14) is equivalent to the field equation (7)
-- statement:
--   Throughout, $\kappa^2 = 8\pi G$ (units $c=\hbar=1$), $a(t)>0$ is the scale factor of the flat FLRW metric, $H=\dot a/a$ is the Hubble function, $\phi(t)$ is the time-dependent part of the MDO fermionic field, $V$ is its potential, $\rho_m, p_m$ are the energy density and pressure of the other matter components, and $F(\phi) = 1+\kappa^2\phi^2/8$.
--
--   Let $\rho_\phi$, $p_\phi$ be defined by Eqs. (10)–(11). Fix a time $t$ at which $a$, $\dot a$, $\phi$, $\dot\phi$ are differentiable, $V$ is differentiable at $\phi(t)$, $a(t)\neq0$ and $\dot\phi(t)\neq0$. Then the MDO conservation equation (14),
--
--   $$\dot\rho_\phi+3H(\rho_\phi+p_\phi)=0,$$
--
--   holds at $t$ if and only if the field equation (7),
--
--   $$\ddot\phi+3H\dot\phi+\frac{dV}{d\phi}-\frac34\frac{H^2\phi}{(1+\kappa^2\phi^2/8)^2}=0,$$
--
--   holds at $t$. This is the paper's remark that Eq. (14) is equivalent to Eq. (7).
--
--   **Formalization Note** The condition $\dot\phi(t)\neq0$ is needed for the direction (14) $\Rightarrow$ (7); no Friedmann equation is assumed.
-- source:
--   S. H. Pereira, M. E. S. Alves, T. M. Guimarães, "An unified cosmological evolution driven by a mass dimension one fermionic field", Eur. Phys. J. C 79 (2019) 543, https://doi.org/10.1140/epjc/s10052-019-7036-5, p. 3, Eqs. (7), (10), (11), (14) and the sentence "the Eq. (14) is obviously equivalent to the Eq. (7)"

import Mathlib
import Definitions.Def_MDOUnifiedCosmology_model

open MDOUnifiedCosmology Set

namespace MDOUnifiedCosmology

theorem conservation_iff_field_eq (κ : ℝ) (V : ℝ → ℝ) (a φ : ℝ → ℝ) (t : ℝ)
    (ha : DifferentiableAt ℝ a t) (ha' : DifferentiableAt ℝ (deriv a) t) (ha0 : a t ≠ 0)
    (hφ : DifferentiableAt ℝ φ t) (hφ' : DifferentiableAt ℝ (deriv φ) t)
    (hV : DifferentiableAt ℝ V (φ t)) (hφdot : deriv φ t ≠ 0) :
    MDOConservation κ V a φ t ↔ FieldEq κ V a φ t := by
  sorry

end MDOUnifiedCosmology
