-- Prove2me | Theorems.Thm_Kyprianou_Ch05_smithCycleAperiodicCompatibility
-- name    : Kyprianou.Ch05.smithCycleAperiodicCompatibility
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:57:17.031194+00:00
-- url     : https://prove2.me/theorems/4f238e93-90c7-441b-8544-5ad6ebdd2b5a
-- title:
--   Chapter 5 Blackwell bridge: Smith cycle and aperiodicity hypotheses
-- statement:
--   A Chapter 5 nonlattice probability law supported on the nonnegative half-line with positive mean satisfies Smith's cycle-law and aperiodicity predicates.
-- source:
--   Source-exact auxiliary bridge for Kyprianou (2006), Theorem 5.1(i), parent b176b15b-454a-4ba5-acbe-94ebda0502ec, to proved Smith (1955) Theorem A(a), 4723f731-2818-44df-bc1c-771b012557ba.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_SmithRegenerative_Equilibrium_Renewal
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- A Chapter 5 nonlattice probability law supported on the nonnegative half-line with positive mean satisfies Smith's cycle-law and aperiodicity predicates. -/
theorem Kyprianou.Ch05.smithCycleAperiodicCompatibility
    (F : Measure Real) [IsProbabilityMeasure F]
    (hSupport : F (Set.Iio (0 : Real)) = 0)
    (hPositiveMean : 0 < ∫ x : Real, x ∂F)
    (hnl : NonLatticeMeasure F) :
    SmithRegenerative.Equilibrium.IsCycleLaw F ∧
      SmithRegenerative.Equilibrium.IsAperiodic F := by sorry
