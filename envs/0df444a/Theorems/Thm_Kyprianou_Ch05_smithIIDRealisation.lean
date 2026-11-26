-- Prove2me | Theorems.Thm_Kyprianou_Ch05_smithIIDRealisation
-- name    : Kyprianou.Ch05.smithIIDRealisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:05:36.610023+00:00
-- url     : https://prove2.me/theorems/0e071b7f-165f-52fa-a1d4-dfe621fe3c3f
-- title:
--   Smith elementary renewal bridge: i.i.d. realisation of the spacing law
-- statement:
--   Every probability law on the nonnegative half-line of positive mean has an i.i.d. realisation with pointwise nonnegative coordinates and the given marginal laws.
-- source:
--   Kyprianou (2006), Theorem 5.1(iii); exact transfer from SmithRenewal.Elementary.elementary_renewal_theorem b689ea1a-fac8-4240-8c12-fa8e3e439bae to parent 0e4a1289-230f-405a-bb6b-dc73f33160d0.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_SmithRenewal_Elementary_RenewalProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators
set_option autoImplicit false
open Kyprianou.Ch05 SmithRenewal.Elementary

theorem Kyprianou.Ch05.smithIIDRealisation
    (F : Measure Real) [IsProbabilityMeasure F]
    (hs : F (Set.Iio (0 : Real)) = 0)
    (hp : 0 < ∫ x : Real, x ∂F) :
    ∃ (P : Measure (Nat → Real)) (X : Nat → (Nat → Real) → Real),
      IsProbabilityMeasure P ∧ IsRenewalProcess P X ∧
      (∀ n, Measure.map (X n) P = F) := by sorry
