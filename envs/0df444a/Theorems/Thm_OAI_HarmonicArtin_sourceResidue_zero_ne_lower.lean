-- Prove2me | Theorems.Thm_OAI_HarmonicArtin_sourceResidue_zero_ne_lower
-- name    : OAI.HarmonicArtin.sourceResidue_zero_ne_lower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:41:45.099117+00:00
-- url     : https://prove2.me/theorems/a565efc9-2b57-406e-af3e-bca378101a0b
-- title:
--   OAI.HarmonicArtin.sourceResidue_zero_ne_lower: intermediate lemma from OpenAI, Harmonic heights and the Artin K(pi,1) conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HarmonicArtin.salvetti_cover_contractible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Harmonic heights and the Artin K(pi,1) conjecture*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HarmonicArtin.sourceResidue_zero_ne_lower` of [lean/OAI/Topology/ArtinGroups/Harmonic/ResidueHeightZeroVector.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/Harmonic/ResidueHeightZeroVector.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HarmonicArtin`, with `open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix`):
--
--   ```lean
--   theorem sourceResidue_zero_ne_lower (P X:Deligne M) (x:Artin M) (hx:x∈P.val.2)
--       (I:Set S) (hI:I.Nonempty) (hPI:P.val.1⊆I) (q:ℤ) (hq:0<q)
--       (c:S⊕Unit→ℝ) (hc:∀v,0 ≤ c v) (hcSupp:∀v,v∉Sum.inl '' I→c v=0)
--       (hcPos:∀v,v∈Sum.inl '' I→0 < c v)
--       (hcNull:∀v,v∈Sum.inl '' I→(framedCartan M *ᵥ c) v=0)
--       (hE:∀H,ClassCapOn Q (sourceFrameFamily M x H)
--         (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \fusionColorRegion m (Sum.inl '' P.val.1)) q)
--       (hdata:∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' P.val.1) ∨
--         (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→sourceMultiplicity M x q v=c v)
--       (hX:SourceResidueAllowed M false P X q) (hh:sourceResidueHeight M P X q=0) :
--       ∃Y:Deligne M,Y<X ∧ SourceResidueAllowed M false P Y q
--   ```
--
--   **Definitions.** The statement is written with `OAI.HarmonicArtin.Deligne`, `OAI.HarmonicArtin.FiniteFusionEdge`, `OAI.HarmonicArtin.FusionLabel`, `OAI.HarmonicArtin.FusionQuiverArrow`, `OAI.HarmonicArtin.FusionVertex`, `OAI.HarmonicArtin.StringLabel`, `OAI.HarmonicArtin.rightCoset` and `OAI.HarmonicArtin.FusionEdge.multiplicity` (definitions bundle `OAIQ225Ag000` of this split); `OAI.HarmonicArtin.framedCartan` (definitions bundle `OAIQ225Ag001` of this split); `OAI.HarmonicArtin.fusionQuiver` (definitions bundle `OAIQ225Ag002` of this split); `OAI.HarmonicArtin.coxeterFusionEdge`, `OAI.HarmonicArtin.coxeterFusionEdge_symm`, `OAI.HarmonicArtin.fusionColorRegion` and `OAI.HarmonicArtin.fusionLabelSize` (definitions bundle `OAIQ225Ag003` of this split); `OAI.HarmonicArtin.ReversibleQuiver.closedNeighborhood` and `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ClassCapOn` (definitions bundle `OAIQ225Ag005` of this split); `OAI.HarmonicArtin.SourceResidueAllowed`, `OAI.HarmonicArtin.sourceFrameFamily`, `OAI.HarmonicArtin.sourceMultiplicity` and `OAI.HarmonicArtin.sourceResidueHeight` (definitions bundle `OAIQ225Ag011` of this split); `OAI.HarmonicArtin.Artin` and `OAI.HarmonicArtin.IsSpherical` (the published bundle `Def_HarmonicArtin`).
--
--   **Used by.** The proof of `OAI.HarmonicArtin.sourcePositiveBlock_contractible` of this split imports it.
-- source:
--   OpenAI, Harmonic heights and the Artin K(pi,1) conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Harmonic-heights-and-the-Artin-K-pi-1-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/Harmonic/ResidueHeightZeroVector.lean (declaration OAI.HarmonicArtin.sourceResidue_zero_ne_lower)

import Mathlib
import Definitions.Def_HarmonicArtin
import Definitions.Def_OAIQ225Ag011

section

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

theorem sourceResidue_zero_ne_lower (P X:Deligne M) (x:Artin M) (hx:x∈P.val.2)
    (I:Set S) (hI:I.Nonempty) (hPI:P.val.1⊆I) (q:ℤ) (hq:0<q)
    (c:S⊕Unit→ℝ) (hc:∀v,0 ≤ c v) (hcSupp:∀v,v∉Sum.inl '' I→c v=0)
    (hcPos:∀v,v∈Sum.inl '' I→0 < c v)
    (hcNull:∀v,v∈Sum.inl '' I→(framedCartan M *ᵥ c) v=0)
    (hE:∀H,ClassCapOn Q (sourceFrameFamily M x H)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \fusionColorRegion m (Sum.inl '' P.val.1)) q)
    (hdata:∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' P.val.1) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→sourceMultiplicity M x q v=c v)
    (hX:SourceResidueAllowed M false P X q) (hh:sourceResidueHeight M P X q=0) :
    ∃Y:Deligne M,Y<X ∧ SourceResidueAllowed M false P Y q := by
  sorry

end HarmonicArtin

end OAI
end
