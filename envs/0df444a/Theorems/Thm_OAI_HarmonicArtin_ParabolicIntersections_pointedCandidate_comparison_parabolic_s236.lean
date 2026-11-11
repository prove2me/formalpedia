-- Prove2me | Theorems.Thm_OAI_HarmonicArtin_ParabolicIntersections_pointedCandidate_comparison_parabolic_s236
-- name    : OAI.HarmonicArtin.ParabolicIntersections.pointedCandidate_comparison_parabolic_s236
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T20:14:19.984233+00:00
-- url     : https://prove2.me/theorems/a0af4ee4-d169-482c-867a-5af359748af7
-- title:
--   OAI.HarmonicArtin.ParabolicIntersections.pointedCandidate_comparison_parabolic_s236: intermediate lemma from OpenAI, Parabolic intersections in Artin groups
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HarmonicArtin.ParabolicIntersections.unconditional_arbitrary_intersections`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_nonclique_dynamics`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure` and `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Parabolic intersections in Artin groups*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HarmonicArtin.ParabolicIntersections.pointedCandidate_comparison_parabolic` of [lean/OAI/Topology/ArtinGroups/ParabolicIntersections/PointedCandidateComparison.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/ParabolicIntersections/PointedCandidateComparison.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HarmonicArtin.ParabolicIntersections`, with `open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex`, `open CoxeterExchange Geometric`):
--
--   ```lean
--   theorem pointedCandidate_comparison_parabolic_s236 (T J J':Set S) (hT:IsSpherical M T)
--       (z h:Artin M) (hh:h∈artinParabolic M T) (q:ℤ) (p p':S⊕Unit→ℝ)
--       (X:PointedCappedCandidate M f T J z q p) (Y:PointedCappedCandidate M f T J' (h*z) q p') :
--       p=p' ∧ J=J' ∧ h∈artinParabolic M J
--   ```
--
--   **Definitions.** The statement is written with `OAI.HarmonicArtin.IsSpherical` (definitions bundle `OAIQ236Ap000` of this split); `OAI.HarmonicArtin.ParabolicIntersections.PointedCappedCandidate` (definitions bundle `OAIQ236Ap011` of this split); `OAI.HarmonicArtin.Artin`, `OAI.HarmonicArtin.artinParabolic` and `OAI.HarmonicArtin.braidRelators` (the published bundle `Def_ArtinParabolicIntersections`).
--
--   **Used by.** The proof of `OAI.HarmonicArtin.ParabolicIntersections.relative_descending_lower_connected_s236` of this split imports it.
-- source:
--   OpenAI, Parabolic intersections in Artin groups, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Parabolic-intersections-in-Artin-groups-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/ParabolicIntersections/PointedCandidateComparison.lean (declaration OAI.HarmonicArtin.ParabolicIntersections.pointedCandidate_comparison_parabolic)

import Mathlib
import Definitions.Def_ArtinParabolicIntersections
import Definitions.Def_OAIQ236Ap011

section

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)

theorem pointedCandidate_comparison_parabolic_s236 (T J J':Set S) (hT:IsSpherical M T)
    (z h:Artin M) (hh:h∈artinParabolic M T) (q:ℤ) (p p':S⊕Unit→ℝ)
    (X:PointedCappedCandidate M f T J z q p) (Y:PointedCappedCandidate M f T J' (h*z) q p') :
    p=p' ∧ J=J' ∧ h∈artinParabolic M J := by
  sorry

end HarmonicArtin.ParabolicIntersections

end OAI
end
