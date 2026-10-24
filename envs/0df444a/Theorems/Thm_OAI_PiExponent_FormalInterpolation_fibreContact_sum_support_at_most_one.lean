-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_sum_support_at_most_one
-- name    : OAI.PiExponent.FormalInterpolation.fibreContact_sum_support_at_most_one
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:46:44.781213+00:00
-- url     : https://prove2.me/theorems/2e54c60f-573c-4405-849f-7153642235aa
-- title:
--   A natural-number sum with at most one positive term
-- statement:
--   If at most one member of a finite family of natural numbers is positive, then its sum is zero or is equal to one member.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fibreContact_sum_support_at_most_one
    {K : Nat} (a : Fin K → Nat)
    (hexclusive : ∀ j k : Fin K, j ≠ k →
      ¬ (0 < a j ∧ 0 < a k)) :
    (∑ j : Fin K, a j) = 0 ∨
      ∃ j : Fin K, (∑ k : Fin K, a k) = a j := by sorry
