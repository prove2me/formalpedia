-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval10_6_e
-- name    : OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_6_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T09:44:42.151196+00:00
-- url     : https://prove2.me/theorems/473f553e-2e5e-459f-9ab9-dd2e3cf4bbbc
-- title:
--   OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_6_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_6` of [lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block2Row10.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block2Row10.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.GramEntries.Block2`, with `open GramRows GramNormalization GramPolynomial`, `open scoped BigOperators`):
--
--   ```lean
--   theorem entryEval10_6_e (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
--       Integer.Sparse.eval entry10_6 (GramNormalization.eval B) = GramFunctions.Block2.form10.mixedGram GramFunctions.Block2.form6 B
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.Certificate.Integer.Sparse.eval` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.GramNormalization.Key` (definitions bundle `OAIQ106E002` of this split); `OAI.MUB6.Certificate.GramFunctions.Block2.form10`, `OAI.MUB6.Certificate.GramFunctions.Block2.form6` and `OAI.MUB6.Certificate.GramFunctions.LinearForm.mixedGram` (definitions bundle `OAIQ106E018` of this split); `OAI.MUB6.Certificate.GramEntries.Block2.entry10_6` (definitions bundle `OAIQ106E021` of this split); `OAI.MUB6.GramNormalization.eval` (definitions bundle `OAIQ106E151` of this split); `OAI.MUB6.Basis` and `OAI.MUB6.IsMUBFamily` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proofs of `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow10_e` and `OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow6_e` of this split import it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block2Row10.lean (declaration OAI.MUB6.Certificate.GramEntries.Block2.entryEval10_6)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E018
import Definitions.Def_OAIQ106E151

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryEval10_6_e (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_6 (GramNormalization.eval B) = GramFunctions.Block2.form10.mixedGram GramFunctions.Block2.form6 B := by
  sorry

end MUB6.Certificate.GramEntries.Block2

end OAI
end
