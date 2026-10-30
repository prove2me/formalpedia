-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_Spectral_centered_normalizedTail_le_of_sq
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.Spectral.centered_normalizedTail_le_of_sq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:34:32.817133+00:00
-- url     : https://prove2.me/theorems/30ee8177-57e2-4f14-8ea5-3a6fd8101ecc
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.Spectral.centered_normalizedTail_le_of_sq: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.Spectral.centered_normalizedTail_le_of_sq` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/SpectralTail.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/SpectralTail.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.Spectral`, with `open scoped BigOperators`, `open SubexponentialSAT.SubexpSwapMultiplicity SubexponentialSAT.Subexp.SpectralRank`):
--
--   ```lean
--   theorem centered_normalizedTail_le_of_sq {r Q R : ℕ} (ε : ℚ)
--       (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4 * R ≤ Q)
--       (hε : 0 < ε)
--       (hwidth : 32 * ((Q - 1 : ℕ) : ℝ) * Real.log (2 / (ε : ℝ)) ≤ (R : ℝ) ^ 2) :
--       normalizedTail r (Q - 1) (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R ≤ ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.SpectralRank.normalizedTail` (definitions bundle `OAIQ081S021` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator.centered_rationalDefect_rank_relative` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/SpectralTail.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.Spectral.centered_normalizedTail_le_of_sq)

import Mathlib
import Definitions.Def_OAIQ081S014
import Definitions.Def_OAIQ081S021

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Spectral

open scoped BigOperators
open SubexponentialSAT.SubexpSwapMultiplicity SubexponentialSAT.Subexp.SpectralRank

theorem centered_normalizedTail_le_of_sq {r Q R : ℕ} (ε : ℚ)
    (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4 * R ≤ Q)
    (hε : 0 < ε)
    (hwidth : 32 * ((Q - 1 : ℕ) : ℝ) * Real.log (2 / (ε : ℝ)) ≤ (R : ℝ) ^ 2) :
    normalizedTail r (Q - 1) (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R ≤ ε := by
  sorry

end SubexponentialSAT.SqrtLog.Spectral

end OAI.Algorithms
end
