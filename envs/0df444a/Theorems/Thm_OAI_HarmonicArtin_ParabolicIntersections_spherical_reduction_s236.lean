-- Prove2me | Theorems.Thm_OAI_HarmonicArtin_ParabolicIntersections_spherical_reduction_s236
-- name    : OAI.HarmonicArtin.ParabolicIntersections.spherical_reduction_s236
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T20:13:48.500316+00:00
-- url     : https://prove2.me/theorems/51d3cd2e-787f-47e9-b8a6-47b7f5ee7092
-- title:
--   OAI.HarmonicArtin.ParabolicIntersections.spherical_reduction_s236: intermediate lemma from OpenAI, Parabolic intersections in Artin groups
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HarmonicArtin.ParabolicIntersections.unconditional_arbitrary_intersections`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_nonclique_dynamics`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure` and `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Parabolic intersections in Artin groups*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HarmonicArtin.ParabolicIntersections.spherical_reduction` of [lean/OAI/Topology/ArtinGroups/ParabolicIntersections/SphericalReduction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/ParabolicIntersections/SphericalReduction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HarmonicArtin.ParabolicIntersections`, with `open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex`, `open CoxeterExchange Geometric`):
--
--   ```lean
--   theorem spherical_reduction_s236 (Y : Set S) (hY : IsSpherical M Y)
--       (hf : f ∉ Y) (hGcd : PublishedFoldingGcd M Y hY)
--       (hmesh : MeshNilpotent Q (fusionColorRegion m (Sum.inl '' Y)))
--       (hAcyclic : PublishedAcyclicTwist Q)
--       (x : Artin M) (hx : x ∈ artinParabolic M {f}ᶜ) :
--       ReductionAt M (pointedInitial M f) Y x
--   ```
--
--   **Definitions.** The statement is written with `OAI.HarmonicArtin.FiniteFusionEdge`, `OAI.HarmonicArtin.FusionLabel`, `OAI.HarmonicArtin.FusionQuiverArrow`, `OAI.HarmonicArtin.FusionVertex`, `OAI.HarmonicArtin.IsSpherical`, `OAI.HarmonicArtin.StringLabel` and `OAI.HarmonicArtin.FusionEdge.multiplicity` (definitions bundle `OAIQ236Ap000` of this split); `OAI.HarmonicArtin.ParabolicIntersections.ReductionAt` (definitions bundle `OAIQ236Ap001` of this split); `OAI.HarmonicArtin.fusionQuiver` (definitions bundle `OAIQ236Ap002` of this split); `OAI.HarmonicArtin.coxeterFusionEdge`, `OAI.HarmonicArtin.coxeterFusionEdge_symm`, `OAI.HarmonicArtin.fusionColorRegion`, `OAI.HarmonicArtin.fusionLabelSize` and `OAI.HarmonicArtin.ParabolicIntersections.MeshNilpotent` (definitions bundle `OAIQ236Ap003` of this split); `OAI.HarmonicArtin.ParabolicIntersections.PointedFamilySpace` and `OAI.HarmonicArtin.ParabolicIntersections.pointedInitial` (definitions bundle `OAIQ236Ap008` of this split); `OAI.HarmonicArtin.ParabolicIntersections.PublishedAcyclicTwist` (definitions bundle `OAIQ236Ap009` of this split); `OAI.HarmonicArtin.ParabolicIntersections.PublishedFoldingGcd` and `OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction` (definitions bundle `OAIQ236Ap011` of this split); `OAI.HarmonicArtin.Artin`, `OAI.HarmonicArtin.artinParabolic` and `OAI.HarmonicArtin.braidRelators` (the published bundle `Def_ArtinParabolicIntersections`).
--
--   **Used by.** The proofs of `OAI.HarmonicArtin.ParabolicIntersections.exists_minimal_parabolic_s236`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_arbitrary_intersections`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure` and `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections` of this split import it.
-- source:
--   OpenAI, Parabolic intersections in Artin groups, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Parabolic-intersections-in-Artin-groups-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/ParabolicIntersections/SphericalReduction.lean (declaration OAI.HarmonicArtin.ParabolicIntersections.spherical_reduction)

import Mathlib
import Mathlib.Algebra.FreeAlgebra
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.RingTheory.TwoSidedIdeal.Operations
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
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

theorem spherical_reduction_s236 (Y : Set S) (hY : IsSpherical M Y)
    (hf : f ∉ Y) (hGcd : PublishedFoldingGcd M Y hY)
    (hmesh : MeshNilpotent Q (fusionColorRegion m (Sum.inl '' Y)))
    (hAcyclic : PublishedAcyclicTwist Q)
    (x : Artin M) (hx : x ∈ artinParabolic M {f}ᶜ) :
    ReductionAt M (pointedInitial M f) Y x := by
  sorry

end HarmonicArtin.ParabolicIntersections

end OAI
end
