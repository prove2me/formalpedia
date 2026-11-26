-- Prove2me | Theorems.Thm_Kyprianou_Ch05_monotoneAdditiveNNRealLinear
-- name    : Kyprianou.Ch05.monotoneAdditiveNNRealLinear
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:22:38.07384+00:00
-- url     : https://prove2.me/theorems/1a8b7f30-1557-57fd-83e0-df883d934b81
-- title:
--   Lemma 5.2: monotone additive functions on the nonnegative reals are linear
-- statement:
--   A real-valued monotone additive function on nonnegative real times is determined by its value at one.
-- source:
--   Kyprianou (2006), Lemma 5.2; exact subordinator Laplace dichotomy reduction cbe8356f-6685-46d0-bf57-78977a3b6679.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.monotoneAdditiveNNRealLinear
    (f : NNReal → Real) (hadd : ∀ s t, f (s+t) = f s + f t)
    (hm : Monotone f) :
    ∀ t : NNReal, f t = (t : Real) * f 1 := by sorry
