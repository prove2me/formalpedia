-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCenterIdeals_pairwiseComaximal
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeals_pairwiseComaximal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T13:24:14.106078+00:00
-- url     : https://prove2.me/theorems/36736458-046b-47f2-be4e-141c31d73e67
-- title:
--   Distinct logarithmic centers give comaximal ideals
-- statement:
--   The logarithmic center ideals of any two distinct centers are comaximal.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeals_pairwiseComaximal
    {m : Nat} (c₁ c₂ : Fin m → Complex) (T : Fin m → Nat)
    (e : Fin (m + 1) → Nat) (he : ∀ i, 0 < e i) (h : c₁ ≠ c₂) :
    IsCoprime (logarithmicCenterIdeal c₁ T e)
      (logarithmicCenterIdeal c₂ T e) := by sorry
