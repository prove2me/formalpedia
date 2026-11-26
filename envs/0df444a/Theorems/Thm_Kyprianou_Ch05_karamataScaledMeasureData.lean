-- Prove2me | Theorems.Thm_Kyprianou_Ch05_karamataScaledMeasureData
-- name    : Kyprianou.Ch05.karamataScaledMeasureData
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:42:51.171658+00:00
-- url     : https://prove2.me/theorems/aa612e6b-6a48-431b-9a94-65e78157145a
-- title:
--   Dilation and normalisation of a measure transports its Laplace transform and cumulative mass
-- statement:
--   Dilation and normalisation of a measure transports its Laplace transform and cumulative mass
-- source:
--   Kyprianou (2006), Theorem 5.13 and Lemma 5.17. Laplace–Stieltjes Tauberian implication.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.karamataScaledMeasureData
    (U : Measure Real) (c : Real → Real)
    (hs : U (Iio 0) = 0)
    (hfin : ∀ t : Real, 0 < t → positiveLaplace U t ≠ ⊤) :
    ∃ M : Real → Measure Real,
      (∀ x, M x (Iio 0) = 0) ∧
      (∀ x t : Real, 0 < t → positiveLaplace (M x) t ≠ ⊤) ∧
      (∀ x t : Real, 0 < x → 0 ≤ c x → 0 < t →
        (positiveLaplace (M x) t).toReal = c x * (positiveLaplace U (t/x)).toReal) ∧
      (∀ x : Real, 0 < x → 0 ≤ c x →
        (M x (Icc 0 1)).toReal = c x * (U (Icc 0 x)).toReal) := by sorry
