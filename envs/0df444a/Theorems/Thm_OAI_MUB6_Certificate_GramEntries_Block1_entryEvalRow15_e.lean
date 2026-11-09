-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEvalRow15_e
-- name    : OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow15_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T09:41:33.588244+00:00
-- url     : https://prove2.me/theorems/78c860be-e518-4893-b9d9-159de6682c98
-- title:
--   OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow15_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow15` of [lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.GramEntries.Block1`):
--
--   ```lean
--   theorem entryEvalRow15_e (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
--       Integer.Sparse.eval (entries 15 j) (GramNormalization.eval B) =
--         (GramFunctions.Block1.forms 15).mixedGram (GramFunctions.Block1.forms j) B
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.Certificate.Integer.Sparse.eval` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.GramNormalization.Key` (definitions bundle `OAIQ106E002` of this split); `OAI.MUB6.Certificate.GramEntries.Block1.entries` (definitions bundle `OAIQ106E013` of this split); `OAI.MUB6.Certificate.GramFunctions.Block1.forms` and `OAI.MUB6.Certificate.GramFunctions.LinearForm.mixedGram` (definitions bundle `OAIQ106E018` of this split); `OAI.MUB6.GramNormalization.eval` (definitions bundle `OAIQ106E151` of this split); `OAI.MUB6.Basis` and `OAI.MUB6.IsMUBFamily` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proof of `OAI.MUB6.Certificate.GramEntries.Block1.entryEval_e` of this split imports it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block1.lean (declaration OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow15)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E013
import Definitions.Def_OAIQ106E018
import Definitions.Def_OAIQ106E151

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

theorem entryEvalRow15_e (j : Fin 21) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 15 j) (GramNormalization.eval B) =
      (GramFunctions.Block1.forms 15).mixedGram (GramFunctions.Block1.forms j) B := by
  sorry

end MUB6.Certificate.GramEntries.Block1

end OAI
end
