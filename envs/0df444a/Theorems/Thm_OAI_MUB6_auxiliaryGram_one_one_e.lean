-- Prove2me | Theorems.Thm_OAI_MUB6_auxiliaryGram_one_one_e
-- name    : OAI.MUB6.auxiliaryGram_one_one_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T12:56:56.915068+00:00
-- url     : https://prove2.me/theorems/f9cd69fa-55dc-46c7-9fb9-4f18ec63e845
-- title:
--   OAI.MUB6.auxiliaryGram_one_one_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.auxiliaryGram_one_one` of [lean/OAI/Analysis/MutuallyUnbiased/Moments/AuxiliaryGram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/Moments/AuxiliaryGram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6`, with `open scoped BigOperators ComplexConjugate`, `open Matrix`):
--
--   ```lean
--   theorem auxiliaryGram_one_one_e (B : Fin 7 → Basis) (hB : IsMUBFamily B) (a v : Charge) :
--       realGram (auxiliaryF B 1 a) (auxiliaryF B 1 v) =
--         (1 / 5 : ℝ) * mixedMoment B (gramCharges a v) (gramLabels 1 1) +
--         (4 / 5 : ℝ) * mixedMoment B (gramCharges a v) (gramLabels 1 2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.AuxiliarySample` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.auxiliaryF`, `OAI.MUB6.gramCharges`, `OAI.MUB6.gramLabels` and `OAI.MUB6.mixedMoment` (definitions bundle `OAIQ106E010` of this split); `OAI.MUB6.realGram` (definitions bundle `OAIQ106E170` of this split); `OAI.MUB6.Basis`, `OAI.MUB6.Charge`, `OAI.MUB6.Coord` and `OAI.MUB6.IsMUBFamily` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proofs of `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow8_e` and `OAI.MUB6.GramNormalization.eval_normalize_e` of this split import it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/Moments/AuxiliaryGram.lean (declaration OAI.MUB6.auxiliaryGram_one_one)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E010
import Definitions.Def_OAIQ106E170

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix

namespace MUB6

theorem auxiliaryGram_one_one_e (B : Fin 7 → Basis) (hB : IsMUBFamily B) (a v : Charge) :
    realGram (auxiliaryF B 1 a) (auxiliaryF B 1 v) =
      (1 / 5 : ℝ) * mixedMoment B (gramCharges a v) (gramLabels 1 1) +
      (4 / 5 : ℝ) * mixedMoment B (gramCharges a v) (gramLabels 1 2) := by
  sorry

end MUB6

end

end OAI
end
