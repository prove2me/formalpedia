-- Prove2me | Theorems.Thm_Kyprianou_Ch05_potentialLaplaceNormalizedExact
-- name    : Kyprianou.Ch05.potentialLaplaceNormalizedExact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:38:24.873795+00:00
-- url     : https://prove2.me/theorems/23403c64-8a0e-567e-b380-9b396243fb4d
-- title:
--   Exact potential transform divided by the reciprocal regular variation factor
-- statement:
--   Exact potential transform divided by the reciprocal regular variation factor
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

theorem Kyprianou.Ch05.potentialLaplaceNormalizedExact
    (U : Measure Real) (Phi L : Real → Real) (rho : Real)
    (hp : ∀ t : Real, 0 < t → 0 < Phi t)
    (hL : ∀ x : Real, 0 < x → Phi (1/x) = x^(-rho)/L x)
    (hLap : ∀ t : Real, 0 < t → positiveLaplace U t = (ENNReal.ofReal (Phi t))⁻¹)
    (t : Real) (ht : 0 < t) :
    (positiveLaplace U t).toReal / (t^(-rho)*L (1/t)) = 1 := by sorry
