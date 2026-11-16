-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_partitionLists_five
-- name    : OAI.UniversalTensorSquare.partitionLists_five
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-15T21:31:30.949601+00:00
-- url     : https://prove2.me/theorems/bcfea37e-ccaa-41b4-9872-68f11698d09c
-- title:
--   OAI.UniversalTensorSquare.partitionLists_five: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.partitionLists_five` of [lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeFive.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeFive.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns`):
--
--   ```lean
--   lemma partitionLists_five : partitionLists 5 5 5 =
--       {[5],[4,1],[3,2],[3,1,1],[2,2,1],[2,1,1,1],[1,1,1,1,1]}
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.partitionLists` (definitions bundle `OAIQ259US001` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.five_kronecker_pos` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeFive.lean (declaration OAI.UniversalTensorSquare.partitionLists_five)

import Mathlib
import Definitions.Def_OAIQ259US001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Saxl Saxl.Columns
namespace UniversalTensorSquare

noncomputable section

lemma partitionLists_five : partitionLists 5 5 5 =
    {[5],[4,1],[3,2],[3,1,1],[2,2,1],[2,1,1,1],[1,1,1,1,1]} := by
  sorry

universe u

end
end UniversalTensorSquare
end

end OAI
end
