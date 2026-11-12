-- Prove2me | Theorems.Thm_OAI_Saxl_ThreeRow_sixSquare_columns
-- name    : OAI.Saxl.ThreeRow.sixSquare_columns
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T18:16:21.973798+00:00
-- url     : https://prove2.me/theorems/aea23349-246a-4d88-aefe-817aad20866a
-- title:
--   OAI.Saxl.ThreeRow.sixSquare_columns: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Saxl.ThreeRow.sixSquare_columns` of [lean/OAI/RepresentationTheory/UniversalSquare/Specht/ThreeRowLocal.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Specht/ThreeRowLocal.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Saxl.ThreeRow`, with `open scoped TensorProduct`, `open FlagColumns Columns Balance`):
--
--   ```lean
--   lemma sixSquare_columns (m s : ℕ) :
--       sixSquare (blocks (columns m s) (standard 3)) =
--         -generator (pairPositions m) (shortSplit m s) (tripleSplit m s)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.FlagColumns.standard`, `OAI.Saxl.ThreeRow.columns`, `OAI.Saxl.ThreeRow.ones`, `OAI.Saxl.ThreeRow.pairPositions`, `OAI.Saxl.ThreeRow.shortSplit`, `OAI.Saxl.ThreeRow.tripleSplit` and `OAI.Saxl.ThreeRow.twos` (definitions bundle `OAIQ259US001` of this split); `OAI.Saxl.FlagColumns.blocks`, `OAI.Saxl.ThreeRow.generator` and `OAI.Saxl.ThreeRow.sixSquare` (definitions bundle `OAIQ259US006` of this split); `OAI.Saxl.WordSpace` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proof of `OAI.Saxl.Balance.WordPacking.threeRows` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Specht/ThreeRowLocal.lean (declaration OAI.Saxl.ThreeRow.sixSquare_columns)

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped TensorProduct
namespace Saxl.ThreeRow
open FlagColumns Columns Balance

lemma sixSquare_columns (m s : ℕ) :
    sixSquare (blocks (columns m s) (standard 3)) =
      -generator (pairPositions m) (shortSplit m s) (tripleSplit m s) := by
  sorry

end Saxl.ThreeRow
end
end

end OAI
end
