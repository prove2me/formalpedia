-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_candidate_rowLens
-- name    : OAI.UniversalTensorSquare.candidate_rowLens
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-16T02:38:50.260973+00:00
-- url     : https://prove2.me/theorems/cb6487f1-9faa-4ff7-917a-c6df61ad002b
-- title:
--   OAI.UniversalTensorSquare.candidate_rowLens: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.candidate_rowLens` of [lean/OAI/RepresentationTheory/UniversalSquare/Specht/CandidateColumns.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Specht/CandidateColumns.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Balance`):
--
--   ```lean
--   lemma candidate_rowLens {M b δ : ℕ} (hM : 4 ≤ M) :
--       (candidate M b δ).rowLens = [M+b+δ,M-1+b] ++
--         (List.range' 3 (M-4)).reverse ++ List.replicate (b+1) 2 ++ List.replicate (1+δ) 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.candidate` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.degreeTreeAll58` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Specht/CandidateColumns.lean (declaration OAI.UniversalTensorSquare.candidate_rowLens)

import Mathlib
import Definitions.Def_OAIQ259US007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance

lemma candidate_rowLens {M b δ : ℕ} (hM : 4 ≤ M) :
    (candidate M b δ).rowLens = [M+b+δ,M-1+b] ++
      (List.range' 3 (M-4)).reverse ++ List.replicate (b+1) 2 ++ List.replicate (1+δ) 1 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
