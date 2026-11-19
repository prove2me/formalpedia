-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_exceptionalCheck106
-- name    : OAI.UniversalTensorSquare.exceptionalCheck106
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T17:14:31.620635+00:00
-- url     : https://prove2.me/theorems/92d0a26f-b6fd-4d34-90cd-ef5fe8281fa2
-- title:
--   OAI.UniversalTensorSquare.exceptionalCheck106: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.exceptionalCheck106` of [lean/OAI/RepresentationTheory/UniversalSquare/Support/ExceptionalFourteen.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/ExceptionalFourteen.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Balance`):
--
--   ```lean
--   lemma exceptionalCheck106 : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
--       ∀ a ∈ List.range exceptionalRows106.length, ∀ c ∈ List.range exceptionalRows106.length,
--         refinedCheck 106 12 14 (d+1) (e+1) (a+1) (c+1) exceptionalRows106
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.exceptionalRows106` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.refinedCheck` (definitions bundle `OAIQ259US012` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.exceptional_pos106` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/ExceptionalFourteen.lean (declaration OAI.UniversalTensorSquare.exceptionalCheck106)

import Mathlib
import Definitions.Def_OAIQ259US012

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

lemma exceptionalCheck106 : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
    ∀ a ∈ List.range exceptionalRows106.length, ∀ c ∈ List.range exceptionalRows106.length,
      refinedCheck 106 12 14 (d+1) (e+1) (a+1) (c+1) exceptionalRows106 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
