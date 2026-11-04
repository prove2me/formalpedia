-- Prove2me | Theorems.Thm_LandauCriterion_landauLocal_eq_landau
-- name    : LandauCriterion.landauLocal_eq_landau
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T18:52:42.601271+00:00
-- url     : https://prove2.me/theorems/7c98fbb1-b416-4567-9735-f0a910812f36
-- title:
--   The two formalizations of Landau's function agree
-- statement:
--   The locally defined mirror `landauLocal n` (the supremum of permutation orders over `Fin n`) equals the platform's `landau n`. This bridge connects the knapsack decomposition and its converse, which are stated for `landauLocal`, to the goal theorem, which is stated for `landau`.
-- source:
--   Definitions `LandauExplore_landauLocal` and `LandauFunction_landau` on the platform; their bodies are the same supremum, so the bridge is expected to hold definitionally.

import Mathlib
import Definitions.Def_LandauExplore_landauLocal
import Definitions.Def_LandauFunction_landau
open Finset LandauExplore LandauFunction

namespace LandauCriterion
theorem landauLocal_eq_landau (n : ℕ) : landauLocal n = landau n := by sorry
end LandauCriterion
