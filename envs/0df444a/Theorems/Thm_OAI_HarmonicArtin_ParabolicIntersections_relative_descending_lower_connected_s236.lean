-- Prove2me | Theorems.Thm_OAI_HarmonicArtin_ParabolicIntersections_relative_descending_lower_connected_s236
-- name    : OAI.HarmonicArtin.ParabolicIntersections.relative_descending_lower_connected_s236
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T20:13:52.0042+00:00
-- url     : https://prove2.me/theorems/52608435-5732-493b-95e8-5da02b9d8d76
-- title:
--   OAI.HarmonicArtin.ParabolicIntersections.relative_descending_lower_connected_s236: intermediate lemma from OpenAI, Parabolic intersections in Artin groups
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HarmonicArtin.ParabolicIntersections.unconditional_arbitrary_intersections`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_nonclique_dynamics`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure` and `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Parabolic intersections in Artin groups*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HarmonicArtin.ParabolicIntersections.relative_descending_lower_connected` of [lean/OAI/Topology/ArtinGroups/ParabolicIntersections/RelativeLowerConnected.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/ParabolicIntersections/RelativeLowerConnected.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HarmonicArtin.ParabolicIntersections`, with `open CategoryTheory Simplicial`):
--
--   ```lean
--   theorem relative_descending_lower_connected_s236 {Y:Set S} {x:Artin M} (P:RelativeVertex M Y x)
--       (hU:U⊆Set.range (Sum.inl:S→S⊕Unit)) (hf:(.inl f:S⊕Unit)∉U)
--       (hxA:sourceCosetRepresentative M P.val∈artinParabolic M {f}ᶜ)
--       (R Q:RelativeVertex M Y x)
--       (hR:RelativeStrictLower M f U cutoff P R) (hQ:RelativeStrictLower M f U cutoff P Q) :
--       PathWithin (relativeAdjacent M) (RelativeStrictLower M f U cutoff P) R Q
--   ```
--
--   **Definitions.** The statement is written with `OAI.HarmonicArtin.Deligne`, `OAI.HarmonicArtin.IsSpherical` and `OAI.HarmonicArtin.rightCoset` (definitions bundle `OAIQ236Ap000` of this split); `OAI.HarmonicArtin.ParabolicIntersections.PathWithin` (definitions bundle `OAIQ236Ap001` of this split); `OAI.HarmonicArtin.sourceCosetRepresentative` (definitions bundle `OAIQ236Ap008` of this split); `OAI.HarmonicArtin.ParabolicIntersections.RelativeStrictLower`, `OAI.HarmonicArtin.ParabolicIntersections.RelativeVertex` and `OAI.HarmonicArtin.ParabolicIntersections.relativeAdjacent` (definitions bundle `OAIQ236Ap011` of this split); `OAI.HarmonicArtin.Artin`, `OAI.HarmonicArtin.artinParabolic` and `OAI.HarmonicArtin.braidRelators` (the published bundle `Def_ArtinParabolicIntersections`).
--
--   **Used by.** The proofs of `OAI.HarmonicArtin.ParabolicIntersections.exists_minimal_parabolic_s236`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_arbitrary_intersections`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure` and `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections` of this split import it.
-- source:
--   OpenAI, Parabolic intersections in Artin groups, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Parabolic-intersections-in-Artin-groups-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/ParabolicIntersections/RelativeLowerConnected.lean (declaration OAI.HarmonicArtin.ParabolicIntersections.relative_descending_lower_connected)

import Mathlib
import Definitions.Def_ArtinParabolicIntersections
import Definitions.Def_OAIQ236Ap011

section

attribute [-instance] _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open CategoryTheory Simplicial
attribute [local instance] Classical.decEq Classical.propDecidable

variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

theorem relative_descending_lower_connected_s236 {Y:Set S} {x:Artin M} (P:RelativeVertex M Y x)
    (hU:U⊆Set.range (Sum.inl:S→S⊕Unit)) (hf:(.inl f:S⊕Unit)∉U)
    (hxA:sourceCosetRepresentative M P.val∈artinParabolic M {f}ᶜ)
    (R Q:RelativeVertex M Y x)
    (hR:RelativeStrictLower M f U cutoff P R) (hQ:RelativeStrictLower M f U cutoff P Q) :
    PathWithin (relativeAdjacent M) (RelativeStrictLower M f U cutoff P) R Q := by
  sorry

end HarmonicArtin.ParabolicIntersections

end OAI
end
