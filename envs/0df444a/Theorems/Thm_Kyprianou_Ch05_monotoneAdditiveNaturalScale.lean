-- Prove2me | Theorems.Thm_Kyprianou_Ch05_monotoneAdditiveNaturalScale
-- name    : Kyprianou.Ch05.monotoneAdditiveNaturalScale
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T17:25:36.060232+00:00
-- url     : https://prove2.me/theorems/a7e9bbad-8de8-501f-9d40-5b65bd1fe72e
-- title:
--   Additivity implies natural scaling by induction.
-- statement:
--   Additivity implies natural scaling by induction.
-- source:
--   Kyprianou (2006), Lemma 5.2; faithful further decomposition of the time-Laplace semigroup and monotone additive linearity.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.monotoneAdditiveNaturalScale
    (f : NNReal → Real) (hadd : ∀ s t, f (s+t) = f s + f t)
    (hm : Monotone f) :
    ∀ (n : Nat) (t : NNReal), f (n • t) = (n : Real) * f t := by sorry
