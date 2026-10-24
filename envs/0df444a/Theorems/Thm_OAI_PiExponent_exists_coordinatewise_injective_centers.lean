-- Prove2me | Theorems.Thm_OAI_PiExponent_exists_coordinatewise_injective_centers
-- name    : OAI.PiExponent.exists_coordinatewise_injective_centers
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:13:39.840359+00:00
-- url     : https://prove2.me/theorems/2c6e06ea-c3c7-4aca-b458-832a4c2c6ebc
-- title:
--   Centers distinct in every coordinate
-- statement:
--   For any finite numbers of centers and coordinates, a complex center family can be chosen injective in every coordinate.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Definitions.Def_PiExponent_DeterminantSetup

theorem OAI.PiExponent.exists_coordinatewise_injective_centers
    (m K : ℕ) :
    ∃ c : Fin K → Fin m → ℂ,
      ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i) := by sorry
