-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_originalNodeEval88_e
-- name    : OAI.MUB6.Certificate.MixedTargetSemantics.originalNodeEval88_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T06:08:30.06965+00:00
-- url     : https://prove2.me/theorems/16aa23c2-f2ec-4cdd-844c-892503ac72dd
-- title:
--   OAI.MUB6.Certificate.MixedTargetSemantics.originalNodeEval88_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.MixedTargetSemantics.originalNodeEval88` of [lean/OAI/Analysis/MutuallyUnbiased/MixedTargets/OriginalMerge5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedTargets/OriginalMerge5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.MixedTargetSemantics`):
--
--   ```lean
--   theorem originalNodeEval88_e (x : OriginalKey → ℝ) :
--       Integer.Sparse.eval originalNode88 x =
--         Integer.Sparse.eval keyPolynomialNode88 (fun i => Integer.Sparse.eval (keyMomentRows i) x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.Certificate.Integer.Sparse.eval` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.Certificate.MixedTargetSemantics.OriginalKey` (definitions bundle `OAIQ106E105` of this split); `OAI.MUB6.Certificate.MixedTargetSemantics.keyPolynomialNode88` (definitions bundle `OAIQ106E123` of this split); `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentRows` (definitions bundle `OAIQ106E130` of this split); `OAI.MUB6.Certificate.MixedTargetSemantics.originalNode88` (definitions bundle `OAIQ106E135` of this split).
--
--   **Used by.** The proof of `OAI.MUB6.family_size_le_five_e` of this split imports it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedTargets/OriginalMerge5.lean (declaration OAI.MUB6.Certificate.MixedTargetSemantics.originalNodeEval88)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E130
import Definitions.Def_OAIQ106E135

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalNodeEval88_e (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalNode88 x =
      Integer.Sparse.eval keyPolynomialNode88 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  sorry

end MUB6.Certificate.MixedTargetSemantics

end OAI
end
