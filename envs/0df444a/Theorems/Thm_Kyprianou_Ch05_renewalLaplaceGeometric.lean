-- Prove2me | Theorems.Thm_Kyprianou_Ch05_renewalLaplaceGeometric
-- name    : Kyprianou.Ch05.renewalLaplaceGeometric
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:18:13.648977+00:00
-- url     : https://prove2.me/theorems/73b492d6-df88-51f8-835c-c9d8e3b21872
-- title:
--   Lemma 5.2: Laplace transform of a probability renewal measure
-- statement:
--   The nonnegative Laplace transform of the sum of convolution powers of a probability measure is the extended-real geometric series, including the infinite boundary case.
-- source:
--   Kyprianou (2006), Lemma 5.2; exact reduction of 236fd4ab-a605-4b79-a83b-a3aaf7704a5b.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.renewalLaplaceGeometric
    (F : Measure Real) [IsProbabilityMeasure F] (theta : Real) :
    (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-theta * x)) ∂(renewalMeasure F)) =
      (1 - (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-theta * x)) ∂(F)))⁻¹ := by sorry
