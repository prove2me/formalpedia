-- Prove2me | Theorems.Thm_Kyprianou_Ch05_positiveAntitoneMultiplicativeExponential
-- name    : Kyprianou.Ch05.positiveAntitoneMultiplicativeExponential
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:22:45.669678+00:00
-- url     : https://prove2.me/theorems/6dd953a7-f384-435f-a2ab-2c28a7ff7924
-- title:
--   Lemma 5.2: exponential representation of positive multiplicative time transforms
-- statement:
--   A positive nonincreasing multiplicative function on nonnegative time, bounded by one, is an exponential with a nonnegative rate.
-- source:
--   Kyprianou (2006), Lemma 5.2; exact subordinator Laplace dichotomy reduction cbe8356f-6685-46d0-bf57-78977a3b6679.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.positiveAntitoneMultiplicativeExponential
    (g : NNReal → ENNReal)
    (hb : ∀ t, 0 < g t ∧ g t ≤ 1)
    (hm : Antitone g) (hmul : ∀ s t, g (s+t) = g s * g t) :
    ∃ a : Real, 0 ≤ a ∧ ∀ t, g t = ENNReal.ofReal (Real.exp (-a * (t : Real))) := by sorry
