-- Prove2me | Theorems.Thm_OAI_HarmonicArtin_ParabolicIntersections_exists_minimal_parabolic_s236
-- name    : OAI.HarmonicArtin.ParabolicIntersections.exists_minimal_parabolic_s236
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:44:44.300134+00:00
-- url     : https://prove2.me/theorems/6bc62187-2861-426a-ac41-62bee5973f76
-- title:
--   OAI.HarmonicArtin.ParabolicIntersections.exists_minimal_parabolic_s236: intermediate lemma from OpenAI, Parabolic intersections in Artin groups
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HarmonicArtin.ParabolicIntersections.unconditional_arbitrary_intersections`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_nonclique_dynamics`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure` and `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Parabolic intersections in Artin groups*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HarmonicArtin.ParabolicIntersections.exists_minimal_parabolic` of [lean/OAI/Topology/ArtinGroups/ParabolicIntersections/ParabolicMinimal.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/ParabolicIntersections/ParabolicMinimal.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HarmonicArtin.ParabolicIntersections`):
--
--   ```lean
--   theorem exists_minimal_parabolic_s236 (F : Set (Subgroup (Artin M))) (hF : F.Nonempty)
--       (hpar : ∀ P∈F, IsParabolic M P) :
--       ∃ P∈F, ∀ Q∈F, Q≤P → Q=P
--   ```
--
--   **Definitions.** The statement is written with `OAI.HarmonicArtin.Artin`, `OAI.HarmonicArtin.braidRelators` and `OAI.HarmonicArtin.ParabolicIntersections.IsParabolic` (the published bundle `Def_ArtinParabolicIntersections`).
--
--   **Used by.** The proof of `OAI.HarmonicArtin.ParabolicIntersections.unconditional_nonclique_dynamics` of this split imports it.
-- source:
--   OpenAI, Parabolic intersections in Artin groups, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Parabolic-intersections-in-Artin-groups-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/ParabolicIntersections/ParabolicMinimal.lean (declaration OAI.HarmonicArtin.ParabolicIntersections.exists_minimal_parabolic)

import Mathlib
import Mathlib.Algebra.FreeAlgebra
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Topology.MetricSpace.Isometry
import Definitions.Def_ArtinParabolicIntersections

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

theorem exists_minimal_parabolic_s236 (F : Set (Subgroup (Artin M))) (hF : F.Nonempty)
    (hpar : ∀ P∈F, IsParabolic M P) :
    ∃ P∈F, ∀ Q∈F, Q≤P → Q=P := by
  sorry

end HarmonicArtin.ParabolicIntersections

end OAI
end
