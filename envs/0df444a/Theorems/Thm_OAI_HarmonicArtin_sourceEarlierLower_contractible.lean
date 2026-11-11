-- Prove2me | Theorems.Thm_OAI_HarmonicArtin_sourceEarlierLower_contractible
-- name    : OAI.HarmonicArtin.sourceEarlierLower_contractible
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:42:38.111769+00:00
-- url     : https://prove2.me/theorems/a959446f-42f0-4eaa-93d0-2b925a5a2911
-- title:
--   OAI.HarmonicArtin.sourceEarlierLower_contractible: intermediate lemma from OpenAI, Harmonic heights and the Artin K(pi,1) conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HarmonicArtin.salvetti_cover_contractible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Harmonic heights and the Artin K(pi,1) conjecture*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HarmonicArtin.sourceEarlierLower_contractible` of [lean/OAI/Topology/ArtinGroups/Harmonic/EarlierLowerOrderIso.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/Harmonic/EarlierLowerOrderIso.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HarmonicArtin`, with `open CategoryTheory Simplicial`):
--
--   ```lean
--   lemma sourceEarlierLower_contractible (P:Deligne M) (h:Nonempty (SourceEarlierLower M P)) :
--       ContractibleSpace |nerve (SourceEarlierLower M P)|
--   ```
--
--   **Definitions.** The statement is written with `OAI.HarmonicArtin.Deligne` and `OAI.HarmonicArtin.rightCoset` (definitions bundle `OAIQ225Ag000` of this split); `OAI.HarmonicArtin.SourceEarlier` and `OAI.HarmonicArtin.SourceEarlierLower` (definitions bundle `OAIQ225Ag011` of this split); `OAI.HarmonicArtin.Artin` and `OAI.HarmonicArtin.IsSpherical` (the published bundle `Def_HarmonicArtin`).
--
--   **Used by.** The proof of `OAI.HarmonicArtin.salvetti_cover_contractible` of this split imports it.
-- source:
--   OpenAI, Harmonic heights and the Artin K(pi,1) conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Harmonic-heights-and-the-Artin-K-pi-1-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/Harmonic/EarlierLowerOrderIso.lean (declaration OAI.HarmonicArtin.sourceEarlierLower_contractible)

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
open CategoryTheory Simplicial

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceEarlierLower_contractible (P:Deligne M) (h:Nonempty (SourceEarlierLower M P)) :
    ContractibleSpace |nerve (SourceEarlierLower M P)| := by
  sorry

end HarmonicArtin

end OAI
end
