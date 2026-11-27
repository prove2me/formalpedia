-- Prove2me | Theorems.Thm_Kyprianou_Ch05_renewalPotentialSubtractOriginV1
-- name    : Kyprianou.Ch05.renewalPotentialSubtractOriginV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:20:34.721289+00:00
-- url     : https://prove2.me/theorems/20c36a01-f873-5425-b7a0-3b2e88c897b3
-- title:
--   Transfer renewal asymptotics after removal of the origin atom
-- statement:
--   Apply the classical renewal theorem and remove the single Dirac mass at zero using local finiteness.
-- source:
--   Kyprianou (2006), Corollary 5.3, p. 114; reduction of fcb23456-1e1f-487b-828b-a95cacc96d37.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.renewalPotentialSubtractOriginV1
    (F V : Measure Real) [IsProbabilityMeasure F]
    (hSupport : F (Set.Iio (0 : Real)) = 0)
    (hFiniteMean : Integrable (fun x : Real => x) F)
    (hPositiveMean : 0 < ∫ x : Real, x ∂F)
    (hRenewal : renewalMeasure F = Measure.dirac (0 : Real) + V)
    (hNonLattice : NonLatticeMeasure V → NonLatticeMeasure F) :
    let mu := ∫ x : Real, x ∂F
    ((NonLatticeMeasure V → ∀ y : Real, 0 < y →
      Tendsto (fun x : Real => (V (Set.Ioc x (x+y))).toReal)
        atTop (nhds (y / mu))) ∧
      Tendsto (fun x : Real => (V (Set.Icc 0 x)).toReal / x)
        atTop (nhds (1 / mu))) := by sorry
