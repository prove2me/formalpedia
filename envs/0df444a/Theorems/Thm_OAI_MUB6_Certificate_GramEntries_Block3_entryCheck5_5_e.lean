-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryCheck5_5_e
-- name    : OAI.MUB6.Certificate.GramEntries.Block3.entryCheck5_5_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T13:08:16.494974+00:00
-- url     : https://prove2.me/theorems/6055b9de-5c73-4fb7-965e-7cce51e27de1
-- title:
--   OAI.MUB6.Certificate.GramEntries.Block3.entryCheck5_5_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.GramEntries.Block3.entryCheck5_5` of [lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block3Row5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block3Row5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.GramEntries.Block3`, with `open GramRows GramNormalization GramPolynomial`, `open scoped BigOperators`):
--
--   ```lean
--   theorem entryCheck5_5_e : entry5_5 =
--       Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form5.size
--         (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form5.terms k).coefficient) (rows5_5 k))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.Certificate.Integer.Sparse` and `OAI.MUB6.Certificate.Integer.Sparse.scale` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.GramNormalization.Key` and `OAI.MUB6.Certificate.GramPolynomial.keyLess` (definitions bundle `OAIQ106E002` of this split); `OAI.MUB6.Certificate.GramFunctions.TaggedTerm` and `OAI.MUB6.Certificate.Integer.Sparse.collectLevels` (definitions bundle `OAIQ106E010` of this split); `OAI.MUB6.Certificate.GramFunctions.Block3.form5` (definitions bundle `OAIQ106E018` of this split); `OAI.MUB6.Certificate.GramEntries.Block3.entry5_5` (definitions bundle `OAIQ106E025` of this split); `OAI.MUB6.Certificate.GramEntries.Block3.rows5_5` (definitions bundle `OAIQ106E031` of this split); `OAI.MUB6.Certificate.GramFunctions.LinearForm` (definitions bundle `OAIQ106E196` of this split).
--
--   **Used by.** The proof of `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_5_e` of this split imports it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block3Row5.lean (declaration OAI.MUB6.Certificate.GramEntries.Block3.entryCheck5_5)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E025
import Definitions.Def_OAIQ106E031

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck5_5_e : entry5_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form5.terms k).coefficient) (rows5_5 k)) := by
  sorry

end MUB6.Certificate.GramEntries.Block3

end OAI
end
