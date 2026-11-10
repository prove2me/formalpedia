-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_MixedTargetSemantics_reducedMergeEval358_e
-- name    : OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval358_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-08T08:34:39.075734+00:00
-- url     : https://prove2.me/theorems/19c2f9e7-09f8-4969-9fd8-5d1487af0191
-- title:
--   OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval358_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval358` of [lean/OAI/Analysis/MutuallyUnbiased/MixedTargets/ReductionMergeSound11.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedTargets/ReductionMergeSound11.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.MixedTargetSemantics`, with `open MixedSemantics`):
--
--   ```lean
--   theorem reducedMergeEval358_e (B : Fin 7 → Basis) (hB : IsMUBFamily B)
--       (hF : AllTransitionsFourierZero B) :
--       Integer.Sparse.eval reducedMerge358 (mixedVector B) =
--         (37623398400 : ℝ) * Integer.Sparse.eval originalMerge358 (originalVector B)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.AllTransitionsFourierZero` and `OAI.MUB6.Certificate.Integer.Sparse.eval` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.Certificate.MixedSemantics.Master` (definitions bundle `OAIQ106E002` of this split); `OAI.MUB6.Certificate.MixedSemantics.mixedVector` (definitions bundle `OAIQ106E086` of this split); `OAI.MUB6.Certificate.MixedTargetSemantics.OriginalKey` (definitions bundle `OAIQ106E105` of this split); `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge358` (definitions bundle `OAIQ106E122` of this split); `OAI.MUB6.Certificate.MixedTargetSemantics.originalMerge358` (definitions bundle `OAIQ106E130` of this split); `OAI.MUB6.Certificate.MixedTargetSemantics.originalVector` (definitions bundle `OAIQ106E137` of this split); `OAI.MUB6.Basis` and `OAI.MUB6.IsMUBFamily` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proof of `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval385_e` of this split imports it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedTargets/ReductionMergeSound11.lean (declaration OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval358)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E122
import Definitions.Def_OAIQ106E130
import Definitions.Def_OAIQ106E137

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval358_e (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge358 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge358 (originalVector B) := by
  sorry

end MUB6.Certificate.MixedTargetSemantics

end OAI
end
