-- Prove2me | Theorems.Thm_OAI_HarmonicArtin_ParabolicIntersections_spherical_mesh_input_s236
-- name    : OAI.HarmonicArtin.ParabolicIntersections.spherical_mesh_input_s236
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T20:23:16.986568+00:00
-- url     : https://prove2.me/theorems/3b55457c-e90f-4467-898c-315ab5f10284
-- title:
--   OAI.HarmonicArtin.ParabolicIntersections.spherical_mesh_input_s236: intermediate lemma from OpenAI, Parabolic intersections in Artin groups
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HarmonicArtin.ParabolicIntersections.unconditional_arbitrary_intersections`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_nonclique_dynamics`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure` and `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Parabolic intersections in Artin groups*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HarmonicArtin.ParabolicIntersections.spherical_mesh_input` of [lean/OAI/Topology/ArtinGroups/ParabolicIntersections/UnconditionalMain.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/ParabolicIntersections/UnconditionalMain.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HarmonicArtin.ParabolicIntersections`):
--
--   ```lean
--   theorem spherical_mesh_input_s236 : PublishedMeshInput M
--   ```
--
--   **Definitions.** The statement is written with `OAI.HarmonicArtin.ParabolicIntersections.PublishedMeshInput` (definitions bundle `OAIQ236Ap011` of this split).
--
--   **Used by.** The proofs of `OAI.HarmonicArtin.ParabolicIntersections.exists_minimal_parabolic_s236`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_arbitrary_intersections`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure` and `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections` of this split import it.
-- source:
--   OpenAI, Parabolic intersections in Artin groups, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Parabolic-intersections-in-Artin-groups-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/ParabolicIntersections/UnconditionalMain.lean (declaration OAI.HarmonicArtin.ParabolicIntersections.spherical_mesh_input)

import Mathlib
import Mathlib.Algebra.FreeAlgebra
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Topology.MetricSpace.Isometry
import Definitions.Def_OAIQ236Ap011

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

theorem spherical_mesh_input_s236 : PublishedMeshInput M := by
  sorry

end HarmonicArtin.ParabolicIntersections

end OAI
end
