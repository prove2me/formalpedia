-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_universal_partition_exceptional
-- name    : OAI.UniversalTensorSquare.universal_partition_exceptional
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-18T14:13:39.763228+00:00
-- url     : https://prove2.me/theorems/7eaadced-ab6b-44ed-b385-f7d4a1b8c280
-- title:
--   OAI.UniversalTensorSquare.universal_partition_exceptional: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.universal_partition_exceptional` of [lean/OAI/RepresentationTheory/UniversalSquare/Main.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Main.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl`):
--
--   ```lean
--   lemma universal_partition_exceptional (n : ℕ)
--       (hexc : exceptionalPair (staircaseIndex n) (remainderPairs n)) :
--       ∃ (lam : YoungDiagram) (hc : lam.card = n),
--         ∀ (μ : YoungDiagram) (hμ : μ.card = n),
--           0 < kronecker (canonicalTableau lam hc) (canonicalTableau lam hc)
--             (canonicalTableau μ hμ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.exceptionalPair` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.remainderPairs` and `OAI.UniversalTensorSquare.staircaseIndex` (definitions bundle `OAIQ259US021` of this split); `OAI.Saxl.canonicalTableau` and `OAI.Saxl.kronecker` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquares.universal_tensor_square` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Main.lean (declaration OAI.UniversalTensorSquare.universal_partition_exceptional)

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma universal_partition_exceptional (n : ℕ)
    (hexc : exceptionalPair (staircaseIndex n) (remainderPairs n)) :
    ∃ (lam : YoungDiagram) (hc : lam.card = n),
      ∀ (μ : YoungDiagram) (hμ : μ.card = n),
        0 < kronecker (canonicalTableau lam hc) (canonicalTableau lam hc)
          (canonicalTableau μ hμ) := by
  sorry

universe u

end UniversalTensorSquare
end
end

end OAI
end
