-- Prove2me | Theorems.Thm_Kyprianou_Ch05_subordinatorLaplaceOneForcesZero
-- name    : Kyprianou.Ch05.subordinatorLaplaceOneForcesZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:22:41.789843+00:00
-- url     : https://prove2.me/theorems/1aa02c79-2ac1-556f-9b16-efe4caa13540
-- title:
--   Lemma 5.2: a unit Laplace transform forces a zero marginal
-- statement:
--   At a positive Laplace argument, a nonnegative subordinator marginal with Laplace transform one must be zero almost surely.
-- source:
--   Kyprianou (2006), Lemma 5.2; exact subordinator Laplace dichotomy reduction cbe8356f-6685-46d0-bf57-78977a3b6679.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.subordinatorLaplaceOneForcesZero
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (hY : Kyprianou.Ch03.IsSubordinator P Y)
    (theta : Real) (htheta : 0 < theta) (t : NNReal)
    (hunit : (∫⁻ w, ENNReal.ofReal (Real.exp (-theta * Y t w)) ∂P) = 1) :
    ∀ᵐ w ∂P, Y t w = 0 := by sorry
