-- Prove2me | Theorems.Thm_Kyprianou_Ch03_stableFracMomentTailPowerIffV1
-- name    : Kyprianou.Ch03.stableFracMomentTailPowerIffV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T15:10:06.617778+00:00
-- url     : https://prove2.me/theorems/f3327e25-b159-4162-a83e-a9e9ea54926b
-- title:
--   Stable Lévy density tail power criterion
-- statement:
--   Restrict to the disjoint positive and negative tails. Transform each weighted density integral to a positive half-line real-power integral using reflection on the negative tail. On the tails max(|x|,1)=|x| and the product with the density is c times |x|^(eta-1-alpha). A nonzero coefficient exists; Mathlib's integrableOn_Ioi_rpow_iff gives eta<alpha.
-- source:
--   Kyprianou (2006), Exercise 3.3(iii), direct application of the shared Theorem 3.8 moment criterion.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.stableFracMomentTailPowerIffV1
    (alpha cPlus cMinus eta : Real)
    (hAlpha : 0 < alpha ∧ alpha < 2)
    (hCPlus : 0 ≤ cPlus) (hCMinus : 0 ≤ cMinus)
    (hNonzero : 0 < cPlus + cMinus)
    (hEta : 0 < eta) :
    IntegrableOn (fun x : Real => (max |x| 1) ^ eta) {x : Real | 1 ≤ |x|}
      ((volume : Measure Real).withDensity
        (fun x : Real => ENNReal.ofReal
          (if 0 < x then cPlus / (x ^ (1 + alpha))
           else if x < 0 then cMinus / ((-x) ^ (1 + alpha))
           else 0))) ↔ eta < alpha := by sorry
