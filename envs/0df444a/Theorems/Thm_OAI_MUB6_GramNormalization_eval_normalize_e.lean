-- Prove2me | Theorems.Thm_OAI_MUB6_GramNormalization_eval_normalize_e
-- name    : OAI.MUB6.GramNormalization.eval_normalize_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T12:58:09.738429+00:00
-- url     : https://prove2.me/theorems/5b228365-36b5-4dc9-a8fa-d1ea5ba4893c
-- title:
--   OAI.MUB6.GramNormalization.eval_normalize_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.GramNormalization.eval_normalize` of [lean/OAI/Analysis/MutuallyUnbiased/Moments/GramNormalization.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/Moments/GramNormalization.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.GramNormalization`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem eval_normalize_e (B : Fin 7 → Basis) (hB : IsMUBFamily B)
--       (s t : Fin 2) (a v : Charge) :
--       eval B (normalize s t a v) = auxiliaryMixedEntry B s t a v
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.auxiliaryMixedEntry` (definitions bundle `OAIQ106E010` of this split); `OAI.MUB6.GramNormalization.normalize` (definitions bundle `OAIQ106E043` of this split); `OAI.MUB6.GramNormalization.eval` (definitions bundle `OAIQ106E151` of this split); `OAI.MUB6.Basis`, `OAI.MUB6.Charge` and `OAI.MUB6.IsMUBFamily` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proofs of `OAI.MUB6.Certificate.GramEntries.Block0.entryEval3_1_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval11_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval12_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval14_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval16_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval19_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval25_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow8_e` and `OAI.MUB6.Certificate.GramEntries.Block5.entryEval2_0_e` of this split import it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/Moments/GramNormalization.lean (declaration OAI.MUB6.GramNormalization.eval_normalize)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E043
import Definitions.Def_OAIQ106E151

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace MUB6.GramNormalization

theorem eval_normalize_e (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (s t : Fin 2) (a v : Charge) :
    eval B (normalize s t a v) = auxiliaryMixedEntry B s t a v := by
  sorry

end MUB6.GramNormalization

end OAI
end
