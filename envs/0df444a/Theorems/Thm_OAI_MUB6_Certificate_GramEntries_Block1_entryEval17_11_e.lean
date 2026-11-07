-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block1_entryEval17_11_e
-- name    : OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_11_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T09:28:37.759455+00:00
-- url     : https://prove2.me/theorems/fd30b322-d19d-4e39-ad02-4a3781e80487
-- title:
--   OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_11_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_11` of [lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block1Row17.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block1Row17.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.GramEntries.Block1`, with `open GramRows GramNormalization GramPolynomial`, `open scoped BigOperators`):
--
--   ```lean
--   theorem entryEval17_11_e (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
--       Integer.Sparse.eval entry17_11 (GramNormalization.eval B) = GramFunctions.Block1.form17.mixedGram GramFunctions.Block1.form11 B
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.Certificate.Integer.Sparse.eval` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.GramNormalization.Key` (definitions bundle `OAIQ106E002` of this split); `OAI.MUB6.Certificate.GramEntries.Block1.entry17_11` (definitions bundle `OAIQ106E013` of this split); `OAI.MUB6.Certificate.GramFunctions.Block1.form17` and `OAI.MUB6.Certificate.GramFunctions.LinearForm.mixedGram` (definitions bundle `OAIQ106E018` of this split); `OAI.MUB6.GramNormalization.eval` (definitions bundle `OAIQ106E151` of this split); `OAI.MUB6.Certificate.GramFunctions.Block1.form11` (definitions bundle `OAIQ106E196` of this split); `OAI.MUB6.Basis` and `OAI.MUB6.IsMUBFamily` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proofs of `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow11_e` and `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow17_e` of this split import it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block1Row17.lean (declaration OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_11)

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

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryEval17_11_e (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry17_11 (GramNormalization.eval B) = GramFunctions.Block1.form17.mixedGram GramFunctions.Block1.form11 B := by
  sorry

end MUB6.Certificate.GramEntries.Block1

end OAI
end
