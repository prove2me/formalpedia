-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_PairTargetSemantics_pair_partition4
-- name    : OAI.MUB6.Certificate.PairTargetSemantics.pair_partition4
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T16:47:18.893976+00:00
-- url     : https://prove2.me/theorems/acf13457-936c-4380-97b7-32a1d844764c
-- title:
--   OAI.MUB6.Certificate.PairTargetSemantics.pair_partition4: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.PairTargetSemantics.pair_partition4` of [lean/OAI/Analysis/MutuallyUnbiased/PairTargets/PartitionRules.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairTargets/PartitionRules.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.PairTargetSemantics`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem pair_partition4 {H : CMatrix} (hH : IsHadamard H)
--       (A : Matrix Coord (Fin 4) ℤ) :
--       pairAverage H (fun K => (∏ j, g K (fun u => A u j)).re) =
--         (1 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 0)) +
--         (5 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 1)) +
--         (5 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 2)) +
--         (5 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 3)) +
--         (5 / 54 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 4)) +
--         (5 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 5)) +
--         (5 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 6)) +
--         (5 / 54 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 7)) +
--         (5 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 8)) +
--         (5 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 9)) +
--         (5 / 54 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 10)) +
--         (5 / 54 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 11)) +
--         (5 / 54 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 12)) +
--         (5 / 54 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 13)) +
--         (5 / 18 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 14))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.injectiveMoment` (definitions bundle `OAIQ106D000` of this split); `OAI.MUB6.groupedColumns`, `OAI.MUB6.EqualityPatterns.family4` and `OAI.MUB6.EqualityPatterns.Family` (definitions bundle `OAIQ106D068` of this split); `OAI.MUB6.pairAverage` (definitions bundle `OAIQ106D140` of this split); `OAI.MUB6.CMatrix`, `OAI.MUB6.Coord`, `OAI.MUB6.IsHadamard` and `OAI.MUB6.g` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proofs of `OAI.MUB6.Certificate.PairTargetSemantics.certificate_zero1`, `OAI.MUB6.Certificate.PairTargetSemantics.expandedIdentity0`, `OAI.MUB6.Certificate.PairTargetSemantics.partition12`, `OAI.MUB6.Certificate.PairTargetSemantics.partition14`, `OAI.MUB6.Certificate.PairTargetSemantics.partition16`, `OAI.MUB6.Certificate.PairTargetSemantics.partition19`, `OAI.MUB6.Certificate.PairTargetSemantics.partition24`, `OAI.MUB6.Certificate.PairTargetSemantics.partition25`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm11`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm13`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm17`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm18`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm21`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm23`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm6`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm7`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm8` and `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm9` of this split import it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairTargets/PartitionRules.lean (declaration OAI.MUB6.Certificate.PairTargetSemantics.pair_partition4)

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106D140

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open scoped BigOperators

theorem pair_partition4 {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix Coord (Fin 4) ℤ) :
    pairAverage H (fun K => (∏ j, g K (fun u => A u j)).re) =
      (1 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 0)) +
      (5 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 1)) +
      (5 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 2)) +
      (5 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 3)) +
      (5 / 54 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 4)) +
      (5 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 5)) +
      (5 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 6)) +
      (5 / 54 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 7)) +
      (5 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 8)) +
      (5 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 9)) +
      (5 / 54 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 10)) +
      (5 / 54 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 11)) +
      (5 / 54 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 12)) +
      (5 / 54 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 13)) +
      (5 / 18 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 14)) := by
  sorry

end MUB6.Certificate.PairTargetSemantics

end OAI
end
