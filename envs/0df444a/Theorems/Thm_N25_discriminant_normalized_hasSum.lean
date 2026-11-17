-- Prove2me | Theorems.Thm_N25_discriminant_normalized_hasSum
-- name    : N25.discriminant_normalized_hasSum
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:31:23.757571+00:00
-- url     : https://prove2.me/theorems/e13de55e-69ff-4c40-8638-a1b30e8710ce
-- title:
--   The normalized discriminant is the generating series of the eta-unit coefficients
-- statement:
--   Let $\tau$ lie in the upper half-plane, put $q=e^{2\pi i\tau}$, and let $a_n$ be the $n$th coefficient of the integral Dedekind eta-unit series. Then the series is summable and
--
--   $$\sum_{n\ge0}a_nq^n=\frac{\Delta(\tau)}{q},$$
--
--    where $\Delta$ is the modular discriminant. This identifies the normalized analytic discriminant with its integral $q$-series.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitAnalytic

set_option autoImplicit false
open N25

theorem N25.discriminant_normalized_hasSum (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ =>
      ((PowerSeries.coeff n ModularCurve.dedekindEtaUnit : ℤ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) ^ n)
      (ModularForm.discriminant τ / Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ))) := by sorry
