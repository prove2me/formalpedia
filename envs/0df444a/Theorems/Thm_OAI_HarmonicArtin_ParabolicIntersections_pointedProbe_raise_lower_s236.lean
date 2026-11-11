-- Prove2me | Theorems.Thm_OAI_HarmonicArtin_ParabolicIntersections_pointedProbe_raise_lower_s236
-- name    : OAI.HarmonicArtin.ParabolicIntersections.pointedProbe_raise_lower_s236
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T20:19:05.087445+00:00
-- url     : https://prove2.me/theorems/e0146702-fa77-4474-a707-5eb8d12f1c46
-- title:
--   OAI.HarmonicArtin.ParabolicIntersections.pointedProbe_raise_lower_s236: intermediate lemma from OpenAI, Parabolic intersections in Artin groups
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HarmonicArtin.ParabolicIntersections.unconditional_arbitrary_intersections`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_nonclique_dynamics`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure` and `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Parabolic intersections in Artin groups*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HarmonicArtin.ParabolicIntersections.pointedProbe_raise_lower` of [lean/OAI/Topology/ArtinGroups/ParabolicIntersections/PointedProbeRaiseLower.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/ParabolicIntersections/PointedProbeRaiseLower.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HarmonicArtin.ParabolicIntersections`, with `open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix`):
--
--   ```lean
--   lemma pointedProbe_raise_lower_s236 (T J:Set S) (z g:Artin M) (q l:ℤ) (p:S⊕Unit→ℝ)
--       (X:PointedCappedCandidate M f T J z q p) (hg:g∈artinParabolic M T) (hl:l<0)
--       (hgz:∀H,ClassCapOn Q (pointedFamily M f (g*z) H)
--         (Set.range (unfoldedInclusion M T)) q)
--       (α:FusionVertex (V:=S⊕Unit) m) (ha:α∈Set.range (unfoldedInclusion M T)) (b:Bool)
--       (hy:ClassLowerBound R l (bw g⁻¹ (initialClass R (.inr (α,b)))))
--       (hsoc:∀j:J,∀L c,classLayerSocleDimension R l (.inl (.inl j,L)) c
--         (bw g⁻¹ (initialClass R (.inr (α,b))))=0) :
--       ClassLowerBound R (l+1) (bw g⁻¹ (initialClass R (.inr (α,b))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.HarmonicArtin.FiniteFusionEdge`, `OAI.HarmonicArtin.FusionLabel`, `OAI.HarmonicArtin.FusionQuiverArrow`, `OAI.HarmonicArtin.FusionVertex`, `OAI.HarmonicArtin.StringLabel` and `OAI.HarmonicArtin.FusionEdge.multiplicity` (definitions bundle `OAIQ236Ap000` of this split); `OAI.HarmonicArtin.ReversibleQuiver.ProbeArrow` and `OAI.HarmonicArtin.ReversibleQuiver.ProbeVertex` (definitions bundle `OAIQ236Ap001` of this split); `OAI.HarmonicArtin.fusionQuiver`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.FiniteHomotopyClass` and `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.initialClass` (definitions bundle `OAIQ236Ap002` of this split); `OAI.HarmonicArtin.coxeterFusionEdge`, `OAI.HarmonicArtin.coxeterFusionEdge_symm`, `OAI.HarmonicArtin.fusionLabelSize` and `OAI.HarmonicArtin.ReversibleQuiver.probeQuiver` (definitions bundle `OAIQ236Ap003` of this split); `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ClassCapOn` (definitions bundle `OAIQ236Ap005` of this split); `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ClassLowerBound` (definitions bundle `OAIQ236Ap006` of this split); `OAI.HarmonicArtin.unfoldedInclusion`, `OAI.HarmonicArtin.ParabolicIntersections.PointedLabel`, `OAI.HarmonicArtin.ParabolicIntersections.pointedFamily` and `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.classLayerSocleDimension` (definitions bundle `OAIQ236Ap008` of this split); `OAI.HarmonicArtin.sourceProbeAction` and `OAI.HarmonicArtin.ParabolicIntersections.PointedCappedCandidate` (definitions bundle `OAIQ236Ap011` of this split); `OAI.HarmonicArtin.Artin`, `OAI.HarmonicArtin.artinParabolic` and `OAI.HarmonicArtin.braidRelators` (the published bundle `Def_ArtinParabolicIntersections`).
--
--   **Used by.** The proof of `OAI.HarmonicArtin.ParabolicIntersections.pointedCandidate_comparison_parabolic_s236` of this split imports it.
-- source:
--   OpenAI, Parabolic intersections in Artin groups, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Parabolic-intersections-in-Artin-groups-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/ParabolicIntersections/PointedProbeRaiseLower.lean (declaration OAI.HarmonicArtin.ParabolicIntersections.pointedProbe_raise_lower)

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
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q
local notation "bw" => sourceProbeAction M (K:=ℂ)

lemma pointedProbe_raise_lower_s236 (T J:Set S) (z g:Artin M) (q l:ℤ) (p:S⊕Unit→ℝ)
    (X:PointedCappedCandidate M f T J z q p) (hg:g∈artinParabolic M T) (hl:l<0)
    (hgz:∀H,ClassCapOn Q (pointedFamily M f (g*z) H)
      (Set.range (unfoldedInclusion M T)) q)
    (α:FusionVertex (V:=S⊕Unit) m) (ha:α∈Set.range (unfoldedInclusion M T)) (b:Bool)
    (hy:ClassLowerBound R l (bw g⁻¹ (initialClass R (.inr (α,b)))))
    (hsoc:∀j:J,∀L c,classLayerSocleDimension R l (.inl (.inl j,L)) c
      (bw g⁻¹ (initialClass R (.inr (α,b))))=0) :
    ClassLowerBound R (l+1) (bw g⁻¹ (initialClass R (.inr (α,b)))) := by
  sorry

end HarmonicArtin.ParabolicIntersections

end OAI
end
