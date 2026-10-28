-- Prove2me | Theorems.Thm_OAI_UniqueGamesTheorem_Decoder_ActualMatrixContradiction_contradiction
-- name    : OAI.UniqueGamesTheorem.Decoder.ActualMatrixContradiction.contradiction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:31:16.680469+00:00
-- url     : https://prove2.me/theorems/9abdd438-efe7-42c2-8b92-4d4a092dcbe6
-- title:
--   OAI.UniqueGamesTheorem.Decoder.ActualMatrixContradiction.contradiction: intermediate lemma from OpenAI, The Unique Games Theorem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniqueGamesTheorem.theorem11`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Unique Games Theorem*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniqueGamesTheorem.Decoder.ActualMatrixContradiction.contradiction` of [lean/OAI/Computability/UniqueGames/Decoding/ActualMatrixContradiction.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/UniqueGames/Decoding/ActualMatrixContradiction.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniqueGamesTheorem.Decoder.ActualMatrixContradiction`, with `open Integration.BinaryLinear Reduction ActualSource Foundations.Games`, `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem contradiction (S : Source)
--       (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
--       (α g₀ β : ℝ) (hα : 0 < α)
--       (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
--       (hβ : 0 ≤ β) (hβ' : β ≤ 1)
--       (hgood : g₀ ≤ ActualGoodRows.adviceMass S k s d r labeling α)
--       (hvariation : ActualProjectedTransfer.slopeVariation k s d β ≤
--         ConstantSelection.variationBudget α g₀ s r)
--       (hrate : (1 - (β / (2 : ℝ) ^ (d + r)) / 3600) ^ k <
--         ConstantSelection.decodingMass α g₀ s r)
--       (hdistinct : S.DistinctNames)
--       (hopt : Clean.IncidenceGap.parityValue (ActualAdviceUpper.sourceIncidence S)
--         (FiniteDistribution.uniform (Fin S.occurrences)) ≤ (4 : ℝ) / 5) : False
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniqueGamesTheorem.Clean.IncidenceGap.parityValue`, `OAI.UniqueGamesTheorem.Reduction.ActualSource.Source` and `OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.uniform` (definitions bundle `OAIQ086U000` of this split); `OAI.UniqueGamesTheorem.Decoder.ConstantSelection.decodingMass` and `OAI.UniqueGamesTheorem.Decoder.ConstantSelection.variationBudget` (definitions bundle `OAIQ086U001` of this split); `OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.sourceIncidence`, `OAI.UniqueGamesTheorem.Decoder.ActualGoodRows.adviceMass`, `OAI.UniqueGamesTheorem.Decoder.ActualProjectedTransfer.slopeVariation`, `OAI.UniqueGamesTheorem.Decoder.TableKeysGame.vertexCount`, `OAI.UniqueGamesTheorem.Reduction.ActualSource.sourceIndexNonempty` and `OAI.UniqueGamesTheorem.Reduction.ActualSource.Source.DistinctNames` (definitions bundle `OAIQ086U003` of this split).
--
--   **Used by.** The proof of `OAI.UniqueGamesTheorem.theorem11` of this split imports it.
-- source:
--   OpenAI, The Unique Games Theorem, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Unique-Games-Theorem-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/UniqueGames/Decoding/ActualMatrixContradiction.lean (declaration OAI.UniqueGamesTheorem.Decoder.ActualMatrixContradiction.contradiction)

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_OAIQ086U003

section

attribute [-instance] _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Decoder.ActualMatrixContradiction

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d r : ℕ}

theorem contradiction (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α g₀ β : ℝ) (hα : 0 < α)
    (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (hgood : g₀ ≤ ActualGoodRows.adviceMass S k s d r labeling α)
    (hvariation : ActualProjectedTransfer.slopeVariation k s d β ≤
      ConstantSelection.variationBudget α g₀ s r)
    (hrate : (1 - (β / (2 : ℝ) ^ (d + r)) / 3600) ^ k <
      ConstantSelection.decodingMass α g₀ s r)
    (hdistinct : S.DistinctNames)
    (hopt : Clean.IncidenceGap.parityValue (ActualAdviceUpper.sourceIncidence S)
      (FiniteDistribution.uniform (Fin S.occurrences)) ≤ (4 : ℝ) / 5) : False := by
  sorry

end
end UniqueGamesTheorem.Decoder.ActualMatrixContradiction

end

end OAI
end
