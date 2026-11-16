-- Prove2me | Theorems.Thm_Kyprianou_Ch05_karamataMonotoneDensityInfinity
-- name    : Kyprianou.Ch05.karamataMonotoneDensityInfinity
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:53:45.841046+00:00
-- url     : https://prove2.me/theorems/ec070bd9-0bf9-442a-ab9f-62bf7d063196
-- title:
--   Theorem 5.14: two-way monotone density Tauberian equivalence
-- statement:
--   For rho>0 and an ultimately monotone nonnegative density u of U, the Laplace asymptotic at theta->0+ is equivalent to u(x)~x^(rho-1)L(x)/Gamma(rho) as x->infinity.
-- source:
--   Kyprianou (2006), first edition, Theorem 5.14, printed p. 127.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Theorem 5.14, p. 127: both directions of the monotone-density theorem. -/
theorem karamataMonotoneDensityInfinity
    (U : Measure Real) (u L : Real → Real) (rho : Real)
    (hL : SlowlyVaryingAtInfinity L)
    (hRho : 0 < rho)
    (hDensity : U =
      ((volume : Measure Real).restrict (Set.Ici 0)).withDensity
        (fun x : Real => ENNReal.ofReal (u x)))
    (hNonnegative : ∀ x : Real, 0 ≤ x → 0 ≤ u x)
    (hEventuallyMonotone : UltimatelyMonotone u) :
    (Tendsto
       (fun theta : Real =>
         (positiveLaplace U theta).toReal /
           (theta ^ (-rho) * L (1 / theta)))
       (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1)) ↔
    (Tendsto
       (fun x : Real =>
         u x / (x ^ (rho - 1) * L x / Real.Gamma rho))
       atTop (nhds 1))
 := by
  sorry

end Kyprianou.Ch05
