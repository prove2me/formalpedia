-- Prove2me | Theorems.Thm_MilnorDynamics_milnorLambdaHalfShift_ne_one
-- name    : MilnorDynamics.milnorLambdaHalfShift_ne_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T12:23:45.809343+00:00
-- url     : https://prove2.me/theorems/e3e8c8e6-e669-4dc3-ad2d-db0b29cd96c1
-- title:
--   The corrected modular lambda is not the constant function $1$
-- statement:
--   Let $\lambda(\tau)=\theta_2(\tau)^4/\theta_3(\tau)^4$ be the classical modular lambda, and let $\lambda_{\mathrm{hs}}$
--   denote the platform function `milnorLambdaHalfShift`, which realises it in the half-shift form
--   $\lambda_{\mathrm{hs}}(\tau)=e^{\pi i\tau}\vartheta_2(\tau/2,\tau)^4/\vartheta_2(0,\tau)^4$. The claim is that this
--   function is not identically $1$.
--
--   This is the minimal sanity check that the corrected definition restored a usable object. The earlier
--   `milnorLambda` was *exactly* the constant $1$, proved remotely in `milnorLambda_published_is_constant`:
--   its numerator $\vartheta_2(0,\tau)$ coincides with the denominator `jacobiTheta tau` by the Mathlib
--   identity `jacobiTheta_eq_jacobiTheta2`, so the ratio was $x/x$. A constant function omits neither $0$
--   nor $1$ only by omitting every value, so every analytic leaf phrased against it was false rather than
--   merely unproved.
--
--   The point is chosen because the value is explicit. At $\tau=2i$ the classical formulas give
--   $$\lambda(2i) = (\sqrt{2}-1)^4 \approx 0.02943725,$$
--   so the function takes a value different from $1$, and the prefactor $e^{\pi i\tau}$ does not cancel it.
--   No analytic estimate is required: this is a single point evaluation, and its role is to certify
--   nonconstancy, not to establish holomorphy, avoidance of $0$ and $1$, surjectivity, or the covering
--   property, which remain separate theorems.
-- source:
--   MilnorLambdaHalfShift (46b2af40-3f5b-4d4c-baad-3cb9839e2382); the countervalue lambda(2i) = (sqrt(2)-1)^4 is classical, cf. Apostol, Modular Functions and Dirichlet Series in Number Theory, Vol. 2, Chapter 2.

import Mathlib
import Definitions.Def_MilnorLambdaHalfShift

open Complex

open MilnorDynamics

namespace MilnorDynamics

/-- The corrected modular lambda `milnorLambdaHalfShift` is not the constant
function.  The earlier `milnorLambda` was identically `1` because its numerator
used `jacobiTheta₂ 0`, which Mathlib proves equals `jacobiTheta`; the corrected
version uses the half-shift argument `τ/2`, and the ratio is genuinely
nonconstant.  This is the minimal sanity check that the correction restored a
usable function. -/
theorem milnorLambdaHalfShift_ne_one :
    milnorLambdaHalfShift (2 * I) ≠ 1 := by
  sorry

end MilnorDynamics
