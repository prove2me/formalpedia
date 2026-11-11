-- Prove2me | Theorems.Thm_OAI_HarmonicArtin_fusionOrbitColor_subobject_separation_s236
-- name    : OAI.HarmonicArtin.fusionOrbitColor_subobject_separation_s236
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T20:14:20.487185+00:00
-- url     : https://prove2.me/theorems/6aa1a58f-5b52-4508-9191-63ca2e7ea12b
-- title:
--   OAI.HarmonicArtin.fusionOrbitColor_subobject_separation_s236: intermediate lemma from OpenAI, Parabolic intersections in Artin groups
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HarmonicArtin.ParabolicIntersections.unconditional_arbitrary_intersections`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_nonclique_dynamics`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure` and `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Parabolic intersections in Artin groups*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HarmonicArtin.fusionOrbitColor_subobject_separation` of [lean/OAI/Topology/ArtinGroups/Harmonic/FusionOrbitColorSubobject.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/Harmonic/FusionOrbitColorSubobject.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HarmonicArtin`, with `open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex`, `open _root_.Matrix _root_.OAI.Matrix`, `open scoped _root_.Matrix _root_.OAI.Matrix BigOperators`):
--
--   ```lean
--   theorem fusionOrbitColor_subobject_separation_s236
--       (w:List (V×Bool)) (s:V) (q k:ℤ) (I J:Set V)
--       (hb:∀ L i,((Y w s L q).placement i).color∉colorBoundary Q (fusionColorRegion m I))
--       {B:Type} {R:B→FusionLabel m→Type} [∀ b L,Fintype (R b L)]
--       (T:∀ b L,BasedComplex Q (K:=ℂ) (R b L))
--       (hT:∀ b L i,((T b L).placement i).level=q)
--       (incl:∀ b L,TermwiseSplitInjection Q (T b L)
--         (fusionOrbitColorLayer m d hd hdiag w s q I hb L))
--       (c:V→ℝ) (σ:B→V→ℝ)
--       (hsvec:∀ b,(∑ L,fusionWeight m L • generatorVector Q (T b L))=fusionFold m (σ b))
--       (hsupp:∀ b L i,((T b L).placement i).color.1∈J)
--       (hσ:∀ b v,v∉J→σ b v=0)
--       (hc:∀ v,0 ≤ c v) (hcSupp:∀ v,v∉I→c v=0) (hcPos:∀ v,v∈I→0 < c v)
--       (hcNull:∀ v,v∈I→(C *ᵥ c) v=0) (hext:∀ v,v∉J→a w s q I v=c v)
--       (hint:(fun j:J=>a w s q I j-c j)∈interior (convexHull ℝ (Set.range fun b:B=>(fun j:J=>σ b j))))
--       (hsoc:∀ H α,α.1∈J→∀ r,coefficientSocle Q (Y w s H k) α r=⊥) :
--       (∀ v∉I,(∃ u∈I,C v u<0)→μ w s k v=0) ∧
--       (∀ j∈J,(C *ᵥ μ w s k) j=0) ∧
--       fusionWeightedHom m d hd (fun L=>fusionOrbitColorLayer m d hd hdiag w s q I hb L)
--         (fun H=>Y w s H k) (k-q)=0 ∧
--       fusionWeightedHom m d hd (fun H=>Y w s H k)
--         (fun L=>fusionOrbitColorLayer m d hd hdiag w s q I hb L) (q-k)=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.HarmonicArtin.FusionEdge`, `OAI.HarmonicArtin.FusionLabel`, `OAI.HarmonicArtin.FusionQuiverArrow`, `OAI.HarmonicArtin.FusionVertex`, `OAI.HarmonicArtin.StringLabel`, `OAI.HarmonicArtin.fusionWeight`, `OAI.HarmonicArtin.FusionEdge.multiplicity`, `OAI.HarmonicArtin.GeneratorPlacement`, `OAI.HarmonicArtin.GeneratorPlacement.level`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex` and `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.FiniteModel` (definitions bundle `OAIQ236Ap000` of this split); `OAI.HarmonicArtin.fusionQuiver` (definitions bundle `OAIQ236Ap002` of this split); `OAI.HarmonicArtin.fusionColorRegion`, `OAI.HarmonicArtin.fusionFold`, `OAI.HarmonicArtin.fusionFoldedCartan`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.coefficientSocle`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.colorBoundary` and `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.generatorVector` (definitions bundle `OAIQ236Ap003` of this split); `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.TermwiseSplitInjection` (definitions bundle `OAIQ236Ap004` of this split); `OAI.HarmonicArtin.FusionOrbitLayerIndex` and `OAI.HarmonicArtin.fusionOrbitModel` (definitions bundle `OAIQ236Ap005` of this split); `OAI.HarmonicArtin.fusionOrbitColorLayer`, `OAI.HarmonicArtin.fusionOrbitLayer` and `OAI.HarmonicArtin.fusionOrbitMultiplicity` (definitions bundle `OAIQ236Ap008` of this split); `OAI.HarmonicArtin.fusionWeightedHom` (definitions bundle `OAIQ236Ap009` of this split); `OAI.HarmonicArtin.fusionOrbitColorMultiplicity` (definitions bundle `OAIQ236Ap012` of this split).
--
--   **Used by.** The proofs of `OAI.HarmonicArtin.IsolatedIterationData.cap_move_s236`, `OAI.HarmonicArtin.IsolatedIterationData.stage_move_s236` and `OAI.HarmonicArtin.ParabolicIntersections.null_boundary_contradiction_s236` of this split import it.
-- source:
--   OpenAI, Parabolic intersections in Artin groups, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Parabolic-intersections-in-Artin-groups-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/Harmonic/FusionOrbitColorSubobject.lean (declaration OAI.HarmonicArtin.fusionOrbitColor_subobject_separation)

import Mathlib
import Definitions.Def_OAIQ236Ap012

section

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix
open scoped _root_.Matrix _root_.OAI.Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E→ℕ) (d:V→V→FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0) (hm:∀ e,2 ≤ m e)
local notation "Q" => fusionQuiver m d hd
local notation "Y" => fusionOrbitLayer m d hd hdiag
local notation "C" => fusionFoldedCartan m d
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "a" => fusionOrbitColorMultiplicity m d hd hdiag hm

theorem fusionOrbitColor_subobject_separation_s236
    (w:List (V×Bool)) (s:V) (q k:ℤ) (I J:Set V)
    (hb:∀ L i,((Y w s L q).placement i).color∉colorBoundary Q (fusionColorRegion m I))
    {B:Type} {R:B→FusionLabel m→Type} [∀ b L,Fintype (R b L)]
    (T:∀ b L,BasedComplex Q (K:=ℂ) (R b L))
    (hT:∀ b L i,((T b L).placement i).level=q)
    (incl:∀ b L,TermwiseSplitInjection Q (T b L)
      (fusionOrbitColorLayer m d hd hdiag w s q I hb L))
    (c:V→ℝ) (σ:B→V→ℝ)
    (hsvec:∀ b,(∑ L,fusionWeight m L • generatorVector Q (T b L))=fusionFold m (σ b))
    (hsupp:∀ b L i,((T b L).placement i).color.1∈J)
    (hσ:∀ b v,v∉J→σ b v=0)
    (hc:∀ v,0 ≤ c v) (hcSupp:∀ v,v∉I→c v=0) (hcPos:∀ v,v∈I→0 < c v)
    (hcNull:∀ v,v∈I→(C *ᵥ c) v=0) (hext:∀ v,v∉J→a w s q I v=c v)
    (hint:(fun j:J=>a w s q I j-c j)∈interior (convexHull ℝ (Set.range fun b:B=>(fun j:J=>σ b j))))
    (hsoc:∀ H α,α.1∈J→∀ r,coefficientSocle Q (Y w s H k) α r=⊥) :
    (∀ v∉I,(∃ u∈I,C v u<0)→μ w s k v=0) ∧
    (∀ j∈J,(C *ᵥ μ w s k) j=0) ∧
    fusionWeightedHom m d hd (fun L=>fusionOrbitColorLayer m d hd hdiag w s q I hb L)
      (fun H=>Y w s H k) (k-q)=0 ∧
    fusionWeightedHom m d hd (fun H=>Y w s H k)
      (fun L=>fusionOrbitColorLayer m d hd hdiag w s q I hb L) (q-k)=0 := by
  sorry

end HarmonicArtin

end OAI
end
