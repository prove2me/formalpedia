-- Prove2me | Theorems.Thm_OAI_HarmonicArtin_sourcePositiveBlock_contractible
-- name    : OAI.HarmonicArtin.sourcePositiveBlock_contractible
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:35:59.123863+00:00
-- url     : https://prove2.me/theorems/8fac718b-201a-4b1d-b2c4-d7d577690d7f
-- title:
--   OAI.HarmonicArtin.sourcePositiveBlock_contractible: intermediate lemma from OpenAI, Harmonic heights and the Artin K(pi,1) conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HarmonicArtin.salvetti_cover_contractible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Harmonic heights and the Artin K(pi,1) conjecture*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HarmonicArtin.sourcePositiveBlock_contractible` of [lean/OAI/Topology/ArtinGroups/Realizations/NegativeBlockContractible.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/Realizations/NegativeBlockContractible.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HarmonicArtin`, with `open scoped _root_.Matrix _root_.OAI.Matrix`, `open CategoryTheory Simplicial ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex`):
--
--   ```lean
--   lemma sourcePositiveBlock_contractible (P:Deligne M) (q:ℕ) (i:S) (_hi:i∈P.val.1)
--       (hp:0 < sourceCosetVector M P q (.inl i))
--       (hn:SourceNullSign M (fun d=>sourceCosetVector M P d) q (.inl i)) :
--       ContractibleSpace (OrderWeights (SourceAllEligibleLower M P))
--   ```
--
--   **Definitions.** The statement is written with `OAI.HarmonicArtin.Deligne` and `OAI.HarmonicArtin.rightCoset` (definitions bundle `OAIQ225Ag000` of this split); `OAI.HarmonicArtin.OrderWeights` and `OAI.HarmonicArtin.SourceNullSign` (definitions bundle `OAIQ225Ag001` of this split); `OAI.HarmonicArtin.instTopologicalSpaceOrderWeights` (definitions bundle `OAIQ225Ag003` of this split); `OAI.HarmonicArtin.SourceAllEligibleLower`, `OAI.HarmonicArtin.SourceEligible` and `OAI.HarmonicArtin.sourceCosetVector` (definitions bundle `OAIQ225Ag011` of this split); `OAI.HarmonicArtin.Artin` and `OAI.HarmonicArtin.IsSpherical` (the published bundle `Def_HarmonicArtin`).
--
--   **Used by.** The proof of `OAI.HarmonicArtin.sourceEarlierLower_contractible` of this split imports it.
-- source:
--   OpenAI, Harmonic heights and the Artin K(pi,1) conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Harmonic-heights-and-the-Artin-K-pi-1-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/Realizations/NegativeBlockContractible.lean (declaration OAI.HarmonicArtin.sourcePositiveBlock_contractible)

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
open scoped _root_.Matrix _root_.OAI.Matrix
open CategoryTheory Simplicial ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourcePositiveBlock_contractible (P:Deligne M) (q:ℕ) (i:S) (_hi:i∈P.val.1)
    (hp:0 < sourceCosetVector M P q (.inl i))
    (hn:SourceNullSign M (fun d=>sourceCosetVector M P d) q (.inl i)) :
    ContractibleSpace (OrderWeights (SourceAllEligibleLower M P)) := by
  sorry

end HarmonicArtin

end OAI
end
