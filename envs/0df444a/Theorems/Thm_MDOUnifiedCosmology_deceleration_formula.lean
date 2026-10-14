-- Prove2me | Theorems.Thm_MDOUnifiedCosmology_deceleration_formula
-- name    : MDOUnifiedCosmology.deceleration_formula
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T13:35:50.347025+00:00
-- url     : https://prove2.me/theorems/9b88e77f-497e-4ace-ace5-8d1d3ae19dbc
-- title:
--   Deceleration parameter $q = -1 - \dot H/H^2$, Eq. (31)
-- statement:
--   Let $a$ be a scale factor that is differentiable at $t$ with $\dot a$ also differentiable at $t$, and suppose $a(t)\neq0$ and $\dot a(t)\neq0$. With $H=\dot a/a$, the deceleration parameter satisfies
--
--   $$q(t)\equiv-\frac{\ddot a\,a}{\dot a^2}=-1-\frac{\dot H}{H^2}.$$
--
--   This is Eq. (31), used to analyse the phantom-like phase at the end of inflation and the reheating epoch.
-- source:
--   S. H. Pereira, M. E. S. Alves, T. M. Guimarães, "An unified cosmological evolution driven by a mass dimension one fermionic field", Eur. Phys. J. C 79 (2019) 543, https://doi.org/10.1140/epjc/s10052-019-7036-5, p. 7, Eq. (31)

import Mathlib
import Definitions.Def_MDOUnifiedCosmology_model

open MDOUnifiedCosmology Set

namespace MDOUnifiedCosmology

theorem deceleration_formula (a : ℝ → ℝ) (t : ℝ) (ha : DifferentiableAt ℝ a t)
    (ha' : DifferentiableAt ℝ (deriv a) t) (ha0 : a t ≠ 0) (had : deriv a t ≠ 0) :
    decelerationParam a t = -1 - deriv (hubble a) t / hubble a t ^ 2 := by
  sorry

end MDOUnifiedCosmology
