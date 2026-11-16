-- Prove2me | Theorems.Thm_Kyprianou_Ch05_karamataTauberianInfinity
-- name    : Kyprianou.Ch05.karamataTauberianInfinity
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:53:17.265028+00:00
-- url     : https://prove2.me/theorems/2fcde82f-3ad7-475a-b4c5-bc516a726620
-- title:
--   Theorem 5.13: two-way Karamata Tauberian equivalence
-- statement:
--   For a measure U supported on [0,infinity), nonnegative rho and a positive slowly varying L, the Laplace transform is asymptotic to theta^(-rho)L(1/theta) as theta decreases to zero if and only if U([0,x]) is asymptotic to x^rho L(x)/Gamma(1+rho) as x tends to infinity. An asymptotic claim demands finite values in the relevant tail.
-- source:
--   Kyprianou (2006), first edition, Theorem 5.13, printed p. 127.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Theorem 5.13, printed p. 127: both directions of Karamata Tauberian equivalence. -/
theorem karamataTauberianInfinity
    (U : Measure Real) (L : Real → Real) (rho : Real)
    (hL : SlowlyVaryingAtInfinity L)
    (hRho : 0 ≤ rho)
    (hSupport : U (Set.Iio (0 : Real)) = 0) :
    (Tendsto
       (fun theta : Real =>
         (positiveLaplace U theta).toReal /
           (theta ^ (-rho) * L (1 / theta)))
       (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1)) ↔
    (Tendsto
       (fun x : Real =>
         (cumulativePotential U x).toReal /
           (x ^ rho * L x / Real.Gamma (1 + rho)))
       atTop (nhds 1)) := by
  sorry

end Kyprianou.Ch05
