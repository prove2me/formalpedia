-- Prove2me | Theorems.Thm_Kyprianou_Ch05_karamataTauberianZero
-- name    : Kyprianou.Ch05.karamataTauberianZero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:54:09.287484+00:00
-- url     : https://prove2.me/theorems/ef0ca1cc-bc74-4ceb-9d34-b9abbac4d14e
-- title:
--   Corollary 5.15: zero-endpoint Tauberian and monotone density equivalences
-- statement:
--   At theta->infinity and x->0+, both directions of Theorems 5.13 and 5.14 remain valid; the slowly varying factor is now slowly varying at zero.
-- source:
--   Kyprianou (2006), first edition, Corollary 5.15, printed p. 127.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Corollary 5.15, p. 127: both Karamata results at the zero endpoint. -/
theorem karamataTauberianZero
    (U : Measure Real) (L : Real → Real) (rho : Real)
    (hL : SlowlyVaryingAtZero L)
    (hRho : 0 ≤ rho)
    (hSupport : U (Set.Iio (0 : Real)) = 0) :
    ((Tendsto
        (fun theta : Real =>
          (positiveLaplace U theta).toReal /
            (theta ^ (-rho) * L (1 / theta)))
        atTop (nhds 1)) ↔
     (Tendsto
        (fun x : Real =>
          (cumulativePotential U x).toReal /
            (x ^ rho * L x / Real.Gamma (1 + rho)))
        (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1))) ∧
    (0 < rho →
      ∀ (u : Real → Real),
        U = ((volume : Measure Real).restrict (Set.Ici 0)).withDensity
          (fun x : Real => ENNReal.ofReal (u x)) →
        (∀ x : Real, 0 ≤ x → 0 ≤ u x) →
        UltimatelyMonotoneAtZero u →
        ((Tendsto
           (fun theta : Real =>
             (positiveLaplace U theta).toReal /
               (theta ^ (-rho) * L (1 / theta)))
           atTop (nhds 1)) ↔
         (Tendsto
           (fun x : Real =>
             u x / (x ^ (rho - 1) * L x / Real.Gamma rho))
           (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1))))
 := by
  sorry

end Kyprianou.Ch05
