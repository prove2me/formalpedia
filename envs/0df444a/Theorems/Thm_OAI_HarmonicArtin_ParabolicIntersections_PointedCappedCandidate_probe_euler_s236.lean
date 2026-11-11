-- Prove2me | Theorems.Thm_OAI_HarmonicArtin_ParabolicIntersections_PointedCappedCandidate_probe_euler_s236
-- name    : OAI.HarmonicArtin.ParabolicIntersections.PointedCappedCandidate.probe_euler_s236
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T20:14:03.366202+00:00
-- url     : https://prove2.me/theorems/9772a818-89d1-4a86-8106-47aed30f6a98
-- title:
--   OAI.HarmonicArtin.ParabolicIntersections.PointedCappedCandidate.probe_euler_s236: intermediate lemma from OpenAI, Parabolic intersections in Artin groups
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HarmonicArtin.ParabolicIntersections.unconditional_arbitrary_intersections`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_nonclique_dynamics`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure` and `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Parabolic intersections in Artin groups*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HarmonicArtin.ParabolicIntersections.PointedCappedCandidate.probe_euler` of [lean/OAI/Topology/ArtinGroups/ParabolicIntersections/PointedCappedCandidate.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/ParabolicIntersections/PointedCappedCandidate.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HarmonicArtin.ParabolicIntersections.PointedCappedCandidate`, with `open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix`):
--
--   ```lean
--   lemma probe_euler_s236 (X:PointedCappedCandidate M f T J z q p)
--       (g:Artin M) (hg:g∈artinParabolic M T)
--       (α:FusionVertex (V:=S⊕Unit) m) (b:Bool) (l:ℤ)
--       (hsoc:∀j:J,∀L c,classLayerSocleDimension R l (.inl (.inl j,L)) c
--         (bw g⁻¹ (initialClass R (.inr (α,b))))=0) :
--       let N:=((minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex.pureLayer R
--         (minimalClassModel_minimal R _) l);
--       (if l=0 then fusionWeight m α.2*p α.1 else 0)-
--         (fun β=>generatorVector R N (.inl β)) ⬝ᵥ fusionFold m (C *ᵥ p) ≤
--         fusionWeight m α.2*pointedMultiplicity M f (g*z) (q-l) α.1
--   ```
--
--   **Definitions.** The statement is written with `OAI.HarmonicArtin.FiniteFusionEdge`, `OAI.HarmonicArtin.FusionLabel`, `OAI.HarmonicArtin.FusionQuiverArrow`, `OAI.HarmonicArtin.FusionVertex`, `OAI.HarmonicArtin.StringLabel`, `OAI.HarmonicArtin.fusionWeight`, `OAI.HarmonicArtin.FusionEdge.multiplicity`, `OAI.HarmonicArtin.GeneratorPlacement.level`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex` and `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.FiniteModel` (definitions bundle `OAIQ236Ap000` of this split); `OAI.HarmonicArtin.ReversibleQuiver.ProbeArrow` and `OAI.HarmonicArtin.ReversibleQuiver.ProbeVertex` (definitions bundle `OAIQ236Ap001` of this split); `OAI.HarmonicArtin.fusionQuiver`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.FiniteHomotopyClass`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.initialClass` and `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.minimalClassModel` (definitions bundle `OAIQ236Ap002` of this split); `OAI.HarmonicArtin.coxeterFusionEdge`, `OAI.HarmonicArtin.coxeterFusionEdge_symm`, `OAI.HarmonicArtin.fusionFold`, `OAI.HarmonicArtin.fusionFoldedCartan`, `OAI.HarmonicArtin.fusionLabelSize`, `OAI.HarmonicArtin.ReversibleQuiver.probeQuiver` and `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.generatorVector` (definitions bundle `OAIQ236Ap003` of this split); `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.minimalClassModel_minimal` and `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.pureLayer` (definitions bundle `OAIQ236Ap005` of this split); `OAI.HarmonicArtin.ParabolicIntersections.pointedMultiplicity` and `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.classLayerSocleDimension` (definitions bundle `OAIQ236Ap008` of this split); `OAI.HarmonicArtin.sourceProbeAction` and `OAI.HarmonicArtin.ParabolicIntersections.PointedCappedCandidate` (definitions bundle `OAIQ236Ap011` of this split); `OAI.HarmonicArtin.Artin`, `OAI.HarmonicArtin.artinParabolic` and `OAI.HarmonicArtin.braidRelators` (the published bundle `Def_ArtinParabolicIntersections`).
--
--   **Used by.** The proofs of `OAI.HarmonicArtin.ParabolicIntersections.pointedCandidate_comparison_parabolic_s236` and `OAI.HarmonicArtin.ParabolicIntersections.pointedProbe_raise_lower_s236` of this split import it.
-- source:
--   OpenAI, Parabolic intersections in Artin groups, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Parabolic-intersections-in-Artin-groups-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/ParabolicIntersections/PointedCappedCandidate.lean (declaration OAI.HarmonicArtin.ParabolicIntersections.PointedCappedCandidate.probe_euler)

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
local notation "C" => fusionFoldedCartan m d

namespace PointedCappedCandidate
variable {M} {f:S} {T J:Set S} {z:Artin M} {q:ℤ} {p:S⊕Unit→ℝ}

lemma probe_euler_s236 (X:PointedCappedCandidate M f T J z q p)
    (g:Artin M) (hg:g∈artinParabolic M T)
    (α:FusionVertex (V:=S⊕Unit) m) (b:Bool) (l:ℤ)
    (hsoc:∀j:J,∀L c,classLayerSocleDimension R l (.inl (.inl j,L)) c
      (bw g⁻¹ (initialClass R (.inr (α,b))))=0) :
    let N:=((minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex.pureLayer R
      (minimalClassModel_minimal R _) l);
    (if l=0 then fusionWeight m α.2*p α.1 else 0)-
      (fun β=>generatorVector R N (.inl β)) ⬝ᵥ fusionFold m (C *ᵥ p) ≤
      fusionWeight m α.2*pointedMultiplicity M f (g*z) (q-l) α.1 := by
  sorry

end PointedCappedCandidate
end HarmonicArtin.ParabolicIntersections

end OAI
end
