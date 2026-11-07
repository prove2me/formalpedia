-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block4_indexed_entry_eval_e
-- name    : OAI.MUB6.Certificate.GramAssembly.Block4.indexed_entry_eval_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T09:02:46.416194+00:00
-- url     : https://prove2.me/theorems/9a53086f-12d5-4379-b7af-7c89f63efd1c
-- title:
--   OAI.MUB6.Certificate.GramAssembly.Block4.indexed_entry_eval_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.GramAssembly.Block4.indexed_entry_eval` of [lean/OAI/Analysis/MutuallyUnbiased/GramAssembly/Block4Semantics.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramAssembly/Block4Semantics.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.GramAssembly.Block4`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem indexed_entry_eval_e (i j : Fin 22) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
--       Integer.Sparse.eval (entries i j) (fun k => GramNormalization.eval B (key k)) =
--         (GramFunctions.Block4.forms i).mixedGram (GramFunctions.Block4.forms j) B
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.Certificate.Integer.Sparse.eval` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.Certificate.GramAssembly.key` (definitions bundle `OAIQ106E002` of this split); `OAI.MUB6.Certificate.GramAssembly.Block4.entries` (definitions bundle `OAIQ106E007` of this split); `OAI.MUB6.Certificate.GramFunctions.Block4.forms` and `OAI.MUB6.Certificate.GramFunctions.LinearForm.mixedGram` (definitions bundle `OAIQ106E018` of this split); `OAI.MUB6.GramNormalization.eval` (definitions bundle `OAIQ106E151` of this split); `OAI.MUB6.Basis` and `OAI.MUB6.IsMUBFamily` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proof of `OAI.MUB6.Certificate.GramAssembly.Block4.polynomial_interpretation_e` of this split imports it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramAssembly/Block4Semantics.lean (declaration OAI.MUB6.Certificate.GramAssembly.Block4.indexed_entry_eval)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E007
import Definitions.Def_OAIQ106E018
import Definitions.Def_OAIQ106E151

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6.Certificate.GramAssembly.Block4

theorem indexed_entry_eval_e (i j : Fin 22) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries i j) (fun k => GramNormalization.eval B (key k)) =
      (GramFunctions.Block4.forms i).mixedGram (GramFunctions.Block4.forms j) B := by
  sorry

end MUB6.Certificate.GramAssembly.Block4

end

end OAI
end
