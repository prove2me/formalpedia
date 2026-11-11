-- Prove2me | Theorems.Thm_OAI_HarmonicArtin_sourceResidue_lower_weights_contractible
-- name    : OAI.HarmonicArtin.sourceResidue_lower_weights_contractible
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:38:41.410846+00:00
-- url     : https://prove2.me/theorems/d8559677-9478-47db-8633-df888f73ed82
-- title:
--   OAI.HarmonicArtin.sourceResidue_lower_weights_contractible: intermediate lemma from OpenAI, Harmonic heights and the Artin K(pi,1) conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HarmonicArtin.salvetti_cover_contractible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Harmonic heights and the Artin K(pi,1) conjecture*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HarmonicArtin.sourceResidue_lower_weights_contractible` of [lean/OAI/Topology/ArtinGroups/Harmonic/ResidueZeroLowerIso.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/Harmonic/ResidueZeroLowerIso.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HarmonicArtin`, with `open Simplicial CategoryTheory`, `open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex`):
--
--   ```lean
--   lemma sourceResidue_lower_weights_contractible {strict:Bool} {P:Deligne M} {q:ℤ}
--       (X:SourceResidue M strict P q) (hh:sourceResidueHeight M P X q<0)
--       (x:Artin M) (hx:x∈P.val.2)
--       (hb:∀H,ClassCapOn Q (sourceFrameFamily M x H) (closedNeighborhood Q (U P.val.1)\U P.val.1) q)
--       (hX:Nonempty (WeightEarlierLower (SourceResidueEarlier M strict P q) X)) :
--       ContractibleSpace (OrderWeights (WeightEarlierLower (SourceResidueEarlier M strict P q) X))
--   ```
--
--   **Definitions.** The statement is written with `OAI.HarmonicArtin.Deligne`, `OAI.HarmonicArtin.FiniteFusionEdge`, `OAI.HarmonicArtin.FusionLabel`, `OAI.HarmonicArtin.FusionQuiverArrow`, `OAI.HarmonicArtin.FusionVertex`, `OAI.HarmonicArtin.StringLabel`, `OAI.HarmonicArtin.rightCoset` and `OAI.HarmonicArtin.FusionEdge.multiplicity` (definitions bundle `OAIQ225Ag000` of this split); `OAI.HarmonicArtin.OrderWeights` and `OAI.HarmonicArtin.WeightEarlierLower` (definitions bundle `OAIQ225Ag001` of this split); `OAI.HarmonicArtin.fusionQuiver` (definitions bundle `OAIQ225Ag002` of this split); `OAI.HarmonicArtin.coxeterFusionEdge`, `OAI.HarmonicArtin.coxeterFusionEdge_symm`, `OAI.HarmonicArtin.fusionLabelSize`, `OAI.HarmonicArtin.instTopologicalSpaceOrderWeights` and `OAI.HarmonicArtin.unfoldedInclusion` (definitions bundle `OAIQ225Ag003` of this split); `OAI.HarmonicArtin.ReversibleQuiver.closedNeighborhood` and `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ClassCapOn` (definitions bundle `OAIQ225Ag005` of this split); `OAI.HarmonicArtin.SourceResidue`, `OAI.HarmonicArtin.SourceResidueAllowed`, `OAI.HarmonicArtin.SourceResidueEarlier`, `OAI.HarmonicArtin.sourceFrameFamily` and `OAI.HarmonicArtin.sourceResidueHeight` (definitions bundle `OAIQ225Ag011` of this split); `OAI.HarmonicArtin.Artin` and `OAI.HarmonicArtin.IsSpherical` (the published bundle `Def_HarmonicArtin`).
--
--   **Used by.** The proof of `OAI.HarmonicArtin.sourcePositiveBlock_contractible` of this split imports it.
-- source:
--   OpenAI, Harmonic heights and the Artin K(pi,1) conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Harmonic-heights-and-the-Artin-K-pi-1-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/Harmonic/ResidueZeroLowerIso.lean (declaration OAI.HarmonicArtin.sourceResidue_lower_weights_contractible)

import Mathlib
import Definitions.Def_HarmonicArtin
import Definitions.Def_OAIQ225Ag011

section

attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open Simplicial CategoryTheory
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "U" => fun J:Set S=>Set.range (unfoldedInclusion M J)

lemma sourceResidue_lower_weights_contractible {strict:Bool} {P:Deligne M} {q:ℤ}
    (X:SourceResidue M strict P q) (hh:sourceResidueHeight M P X q<0)
    (x:Artin M) (hx:x∈P.val.2)
    (hb:∀H,ClassCapOn Q (sourceFrameFamily M x H) (closedNeighborhood Q (U P.val.1)\U P.val.1) q)
    (hX:Nonempty (WeightEarlierLower (SourceResidueEarlier M strict P q) X)) :
    ContractibleSpace (OrderWeights (WeightEarlierLower (SourceResidueEarlier M strict P q) X)) := by
  sorry

end HarmonicArtin

end OAI
end
