-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedContinuousSimplex_volume_aux
-- name    : OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_volume_aux
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T10:06:03.838854+00:00
-- url     : https://prove2.me/theorems/80cc5a73-c88f-4046-9621-61e3448c2222
-- title:
--   Volume of a positive weighted simplex
-- statement:
--   The volume of the nonnegative simplex with positive coordinate weights and height `T` is `T^n` divided by `n!` times the product of the weights. A diagonal coordinate scaling reduces the computation to the standard simplex volume, with positivity of every weight enabling the change of variables. At dimension zero, both sides equal one.

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_volume_aux
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i)
    (T : Real) (hT : 0 < T) :
    ENNReal.toReal
      (MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, w i * x i) < T})
      = T ^ n / ((n.factorial : Real) * Finset.univ.prod w) := by sorry
