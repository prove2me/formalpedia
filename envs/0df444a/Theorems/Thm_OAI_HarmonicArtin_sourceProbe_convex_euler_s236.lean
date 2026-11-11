-- Prove2me | Theorems.Thm_OAI_HarmonicArtin_sourceProbe_convex_euler_s236
-- name    : OAI.HarmonicArtin.sourceProbe_convex_euler_s236
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T20:17:15.652595+00:00
-- url     : https://prove2.me/theorems/9f6cde7c-a576-4682-83fa-480352371270
-- title:
--   OAI.HarmonicArtin.sourceProbe_convex_euler_s236: intermediate lemma from OpenAI, Parabolic intersections in Artin groups
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HarmonicArtin.ParabolicIntersections.unconditional_arbitrary_intersections`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_nonclique_dynamics`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure` and `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Parabolic intersections in Artin groups*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HarmonicArtin.sourceProbe_convex_euler` of [lean/OAI/Topology/ArtinGroups/Geometry/ProbeConvexEuler.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/Geometry/ProbeConvexEuler.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HarmonicArtin`, with `open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex`, `open ReversibleQuiver.ProbeEmbedding _root_.Matrix _root_.OAI.Matrix CoxeterExchange Geometric`):
--
--   ```lean
--   lemma sourceProbe_convex_euler_s236
--       (J:Set S) (hJ:IsSpherical M J) (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit)
--       (q:ℤ) (p:S⊕Unit→ℝ)
--       (hconvex:(μ z s q-p)∈convexHull ℝ (Set.range (sourceConvexVector M J z s q)))
--       (g:Artin M) (α:FusionVertex (V:=S⊕Unit) m) (b:Bool) (l:ℤ)
--       (hsoc:∀j:J,∀L c,coefficientSocle R
--         ((minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex.pureLayer R
--           (minimalClassModel_minimal R _) l) (.inl (.inl (j:S),L)) c=⊥) :
--       let N:=((minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex.pureLayer R
--         (minimalClassModel_minimal R _) l);
--       -(generatorVector R N ⬝ᵥ (unfoldedCartan R *ᵥ Sum.elim (fusionFold m p) (fun _=>0)))≤
--         ∑H,fusionWeight m H*(classLevelArray Q (aw g (O z s H)) (α,q-l):ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.HarmonicArtin.FiniteFusionEdge`, `OAI.HarmonicArtin.FusionLabel`, `OAI.HarmonicArtin.FusionQuiverArrow`, `OAI.HarmonicArtin.FusionVertex`, `OAI.HarmonicArtin.IsSpherical`, `OAI.HarmonicArtin.StringLabel`, `OAI.HarmonicArtin.fusionWeight`, `OAI.HarmonicArtin.CoxeterExchange.restrictedMatrix`, `OAI.HarmonicArtin.FusionEdge.multiplicity`, `OAI.HarmonicArtin.GeneratorPlacement.level`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex` and `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.FiniteModel` (definitions bundle `OAIQ236Ap000` of this split); `OAI.HarmonicArtin.ReversibleQuiver.ProbeArrow` and `OAI.HarmonicArtin.ReversibleQuiver.ProbeVertex` (definitions bundle `OAIQ236Ap001` of this split); `OAI.HarmonicArtin.fusionQuiver`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.FiniteHomotopyClass`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.initialClass` and `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.minimalClassModel` (definitions bundle `OAIQ236Ap002` of this split); `OAI.HarmonicArtin.coxeterFusionEdge`, `OAI.HarmonicArtin.coxeterFusionEdge_diag`, `OAI.HarmonicArtin.coxeterFusionEdge_symm`, `OAI.HarmonicArtin.fusionFold`, `OAI.HarmonicArtin.fusionLabelSize`, `OAI.HarmonicArtin.fusionLabelSize_ge_four`, `OAI.HarmonicArtin.ReversibleQuiver.probeQuiver`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.coefficientSocle` and `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.generatorVector` (definitions bundle `OAIQ236Ap003` of this split); `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.unfoldedCartan` (definitions bundle `OAIQ236Ap004` of this split); `OAI.HarmonicArtin.fusionPacketOrbit`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.classLevelArray`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.minimalClassModel_minimal` and `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.pureLayer` (definitions bundle `OAIQ236Ap005` of this split); `OAI.HarmonicArtin.fusionOrbitMultiplicity` and `OAI.HarmonicArtin.sourceArtinAction` (definitions bundle `OAIQ236Ap008` of this split); `OAI.HarmonicArtin.sourceProbeAction` (definitions bundle `OAIQ236Ap011` of this split); `OAI.HarmonicArtin.sourceConvexVector` (definitions bundle `OAIQ236Ap013` of this split); `OAI.HarmonicArtin.Artin` and `OAI.HarmonicArtin.braidRelators` (the published bundle `Def_ArtinParabolicIntersections`).
--
--   **Used by.** The proof of `OAI.HarmonicArtin.ParabolicIntersections.PointedCappedCandidate.probe_euler_s236` of this split imports it.
-- source:
--   OpenAI, Parabolic intersections in Artin groups, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Parabolic-intersections-in-Artin-groups-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/Geometry/ProbeConvexEuler.lean (declaration OAI.HarmonicArtin.sourceProbe_convex_euler)

import Mathlib
import Definitions.Def_ArtinParabolicIntersections
import Definitions.Def_OAIQ236Ap013

section

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamilyMulAction _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeFamilyMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open ReversibleQuiver.ProbeEmbedding _root_.Matrix _root_.OAI.Matrix CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "hm" => (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Q" => fusionQuiver m d hd
local notation "R" => probeQuiver Q
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "Y" => fusionOrbitLayer m d hd hdiag
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "aw" => sourceArtinAction M (K:=ℂ)
local notation "bw" => sourceProbeAction M (K:=ℂ)

lemma sourceProbe_convex_euler_s236
    (J:Set S) (hJ:IsSpherical M J) (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit)
    (q:ℤ) (p:S⊕Unit→ℝ)
    (hconvex:(μ z s q-p)∈convexHull ℝ (Set.range (sourceConvexVector M J z s q)))
    (g:Artin M) (α:FusionVertex (V:=S⊕Unit) m) (b:Bool) (l:ℤ)
    (hsoc:∀j:J,∀L c,coefficientSocle R
      ((minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex.pureLayer R
        (minimalClassModel_minimal R _) l) (.inl (.inl (j:S),L)) c=⊥) :
    let N:=((minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex.pureLayer R
      (minimalClassModel_minimal R _) l);
    -(generatorVector R N ⬝ᵥ (unfoldedCartan R *ᵥ Sum.elim (fusionFold m p) (fun _=>0)))≤
      ∑H,fusionWeight m H*(classLevelArray Q (aw g (O z s H)) (α,q-l):ℝ) := by
  sorry

end HarmonicArtin

end OAI
end
