-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_exceptionalCheck114
-- name    : OAI.UniversalTensorSquare.exceptionalCheck114
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T17:14:34.990803+00:00
-- url     : https://prove2.me/theorems/84875584-635a-49d5-ad1b-33d0644e4bd5
-- title:
--   OAI.UniversalTensorSquare.exceptionalCheck114: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.exceptionalCheck114` of [lean/OAI/RepresentationTheory/UniversalSquare/Support/ExceptionalFourteen.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/ExceptionalFourteen.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Balance`):
--
--   ```lean
--   lemma exceptionalCheck114 : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
--       ∀ a ∈ List.range exceptionalRows114.length, ∀ c ∈ List.range exceptionalRows114.length,
--         refinedCheck 114 12 18 (d+1) (e+1) (a+1) (c+1) exceptionalRows114
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.exceptionalRows114` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.refinedCheck` (definitions bundle `OAIQ259US012` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.exceptional_pos114` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/ExceptionalFourteen.lean (declaration OAI.UniversalTensorSquare.exceptionalCheck114)

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

lemma exceptionalCheck114 : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
    ∀ a ∈ List.range exceptionalRows114.length, ∀ c ∈ List.range exceptionalRows114.length,
      refinedCheck 114 12 18 (d+1) (e+1) (a+1) (c+1) exceptionalRows114 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
