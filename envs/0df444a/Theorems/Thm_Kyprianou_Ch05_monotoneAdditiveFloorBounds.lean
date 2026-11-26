-- Prove2me | Theorems.Thm_Kyprianou_Ch05_monotoneAdditiveFloorBounds
-- name    : Kyprianou.Ch05.monotoneAdditiveFloorBounds
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T17:25:40.376805+00:00
-- url     : https://prove2.me/theorems/f864894e-ee3d-5b13-aba9-4ed138a36bd5
-- title:
--   Integer floor bounds on both signs of the deviation from linearity, using monotonicity and natural scaling.
-- statement:
--   Integer floor bounds on both signs of the deviation from linearity, using monotonicity and natural scaling.
-- source:
--   Kyprianou (2006), Lemma 5.2; faithful further decomposition of the time-Laplace semigroup and monotone additive linearity.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.monotoneAdditiveFloorBounds
    (f : NNReal → Real) (hadd : ∀ s t, f (s+t) = f s + f t)
    (hm : Monotone f) (t : NNReal) (n : Nat) :
      (n : Real) * (f t - (t : Real) * f 1) ≤ f 1 ∧
      (n : Real) * ((t : Real) * f 1 - f t) ≤ f 1 := by sorry
