-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCenterIdeals_comax_of_ne_coordinate
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeals_comax_of_ne_coordinate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T09:15:26.834988+00:00
-- url     : https://prove2.me/theorems/a17cbb26-5f85-4557-b346-c32f87294a3b
-- title:
--   Logarithmic center ideals for centers differing in a coordinate are comaximal
-- statement:
--   For two logarithmic centers with the same truncation data, if they differ in some coordinate, their generated center ideals are comaximal.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeals_comax_of_ne_coordinate
    {m : Nat} (c d : Fin m → Complex) (T : Fin m → Nat)
    (e : Fin (m + 1) → Nat) (h : ∃ i, c i ≠ d i) :
    IsCoprime (logarithmicCenterIdeal c T e)
      (logarithmicCenterIdeal d T e) := by sorry
