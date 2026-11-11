-- Prove2me | Theorems.Thm_OAI_HarmonicArtin_IsolatedIterationData_separation
-- name    : OAI.HarmonicArtin.IsolatedIterationData.separation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:34:42.567225+00:00
-- url     : https://prove2.me/theorems/b1da9f8f-1aaf-460e-9270-cbb1aff0cf85
-- title:
--   OAI.HarmonicArtin.IsolatedIterationData.separation: intermediate lemma from OpenAI, Harmonic heights and the Artin K(pi,1) conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HarmonicArtin.salvetti_cover_contractible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Harmonic heights and the Artin K(pi,1) conjecture*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HarmonicArtin.IsolatedIterationData.separation` of [lean/OAI/Topology/ArtinGroups/Harmonic/IsolatedIterationData.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/Harmonic/IsolatedIterationData.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HarmonicArtin.IsolatedIterationData`, with `open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex`, `open _root_.Matrix _root_.OAI.Matrix`):
--
--   ```lean
--   lemma separation (z:List ((S⊕Unit)×Bool)) (hz:D.valid z) (hc:D.capped z)
--       (k:ℤ) (hs:D.openSocle z k) :
--       (∀ v∉Sum.inl '' D.I,(∃ u∈Sum.inl '' D.I,C v u<0)→μ z D.s k v=0) ∧
--       (∀ j∈Sum.inl '' D.J,(C *ᵥ μ z D.s k) j=0) ∧
--       fusionWeightedHom m d hd (D.fullRegion z hz) (fun H=>Y z D.s H k) (k-D.q)=0 ∧
--       fusionWeightedHom m d hd (fun H=>Y z D.s H k) (D.fullRegion z hz) (D.q-k)=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.HarmonicArtin.FiniteFusionEdge`, `OAI.HarmonicArtin.FusionLabel`, `OAI.HarmonicArtin.FusionQuiverArrow`, `OAI.HarmonicArtin.FusionVertex`, `OAI.HarmonicArtin.StringLabel`, `OAI.HarmonicArtin.FusionEdge.multiplicity`, `OAI.HarmonicArtin.GeneratorPlacement`, `OAI.HarmonicArtin.GeneratorPlacement.level` and `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex` (definitions bundle `OAIQ225Ag000` of this split); `OAI.HarmonicArtin.fusionQuiver` and `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.FiniteModel` (definitions bundle `OAIQ225Ag002` of this split); `OAI.HarmonicArtin.coxeterFusionEdge`, `OAI.HarmonicArtin.coxeterFusionEdge_diag`, `OAI.HarmonicArtin.coxeterFusionEdge_symm`, `OAI.HarmonicArtin.fusionColorRegion`, `OAI.HarmonicArtin.fusionFoldedCartan`, `OAI.HarmonicArtin.fusionLabelSize` and `OAI.HarmonicArtin.fusionLabelSize_ge_four` (definitions bundle `OAIQ225Ag003` of this split); `OAI.HarmonicArtin.FusionOrbitLayerIndex` and `OAI.HarmonicArtin.fusionOrbitModel` (definitions bundle `OAIQ225Ag005` of this split); `OAI.HarmonicArtin.IsolatedIterationData`, `OAI.HarmonicArtin.fusionOrbitLayer`, `OAI.HarmonicArtin.fusionOrbitMultiplicity`, `OAI.HarmonicArtin.IsolatedIterationData.capped`, `OAI.HarmonicArtin.IsolatedIterationData.fullRegion` and `OAI.HarmonicArtin.IsolatedIterationData.openSocle` (definitions bundle `OAIQ225Ag009` of this split); `OAI.HarmonicArtin.fusionWeightedHom` (definitions bundle `OAIQ225Ag010` of this split).
--
--   **Used by.** The proofs of `OAI.HarmonicArtin.IsolatedIterationData.stage_move` and `OAI.HarmonicArtin.sourceClosedResidue_nonempty` of this split import it.
-- source:
--   OpenAI, Harmonic heights and the Artin K(pi,1) conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Harmonic-heights-and-the-Artin-K-pi-1-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/Harmonic/IsolatedIterationData.lean (declaration OAI.HarmonicArtin.IsolatedIterationData.separation)

import Mathlib
import Definitions.Def_OAIQ225Ag009
import Definitions.Def_OAIQ225Ag010

section

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "hm" => (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Y" => fusionOrbitLayer m d hd hdiag
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "C" => fusionFoldedCartan m d

namespace IsolatedIterationData
variable {M} (D:IsolatedIterationData M)

lemma separation (z:List ((S⊕Unit)×Bool)) (hz:D.valid z) (hc:D.capped z)
    (k:ℤ) (hs:D.openSocle z k) :
    (∀ v∉Sum.inl '' D.I,(∃ u∈Sum.inl '' D.I,C v u<0)→μ z D.s k v=0) ∧
    (∀ j∈Sum.inl '' D.J,(C *ᵥ μ z D.s k) j=0) ∧
    fusionWeightedHom m d hd (D.fullRegion z hz) (fun H=>Y z D.s H k) (k-D.q)=0 ∧
    fusionWeightedHom m d hd (fun H=>Y z D.s H k) (D.fullRegion z hz) (D.q-k)=0 := by
  sorry

end IsolatedIterationData
end HarmonicArtin

end OAI
end
