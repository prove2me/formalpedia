-- Prove2me | Theorems.Thm_Kyprianou_Ch05_karamataTauberianZeroCumulativeFinite
-- name    : Kyprianou.Ch05.karamataTauberianZeroCumulativeFinite
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T20:38:22.728798+00:00
-- url     : https://prove2.me/theorems/e36e134e-c91b-540c-89d4-b7df375f16e1
-- title:
--   Karamata cumulative equivalence at zero with finite positive Laplace transforms
-- statement:
--   Karamata cumulative equivalence at zero with finite positive Laplace transforms
-- source:
--   Kyprianou (2006), Lemma 5.17 and Karamata's theorem, corrected reciprocal factor.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.karamataTauberianZeroCumulativeFinite
    (U : Measure Real) (L : Real → Real) (rho : Real)
    (hL : SlowlyVaryingAtZero L) (hRho : 0 ≤ rho)
    (hSupport : U (Iio (0 : Real)) = 0)
    (hFinite : ∀ t : Real, 0 < t → positiveLaplace U t ≠ ⊤) :
    (Tendsto (fun theta : Real => (positiveLaplace U theta).toReal /
      (theta^(-rho)*L (1/theta))) atTop (nhds 1)) ↔
    (Tendsto (fun x : Real => (cumulativePotential U x).toReal /
      (x^rho*L x/Real.Gamma (1+rho))) (nhdsWithin (0 : Real) (Ioi 0)) (nhds 1)) := by sorry
