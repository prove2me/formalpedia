-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_balance_dominance
-- name    : OAI.UniversalTensorSquare.balance_dominance
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T17:06:17.182255+00:00
-- url     : https://prove2.me/theorems/f6a93de0-9951-4ab3-9b93-2b6594046f8c
-- title:
--   OAI.UniversalTensorSquare.balance_dominance: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.balance_dominance` of [lean/OAI/RepresentationTheory/UniversalSquare/Balance/BalanceDominance.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Balance/BalanceDominance.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl`):
--
--   ```lean
--   theorem balance_dominance (M : ℕ) (hM : 9 ≤ M) (μ A : YoungDiagram)
--       (hc : μ.card = A.card) (hn : (staircase M).card ≤ μ.card)
--       (hμ : colPrefix μ 4 ≤ 2*M-2)
--       (hparts : 2*M-5 ≤ A.colLen 0) (hmax : A.rowLen 0 ≤ M+1)
--       (hfour : 2 ≤ A.rowLen 3) : Dominates μ A
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.staircase` (definitions bundle `OAIQ259US000` of this split); `OAI.Saxl.Dominates` and `OAI.UniversalTensorSquare.colPrefix` (definitions bundle `OAIQ259US001` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.balance_kronecker_pos` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Balance/BalanceDominance.lean (declaration OAI.UniversalTensorSquare.balance_dominance)

import Mathlib
import Definitions.Def_OAIQ259US000
import Definitions.Def_OAIQ259US001

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

theorem balance_dominance (M : ℕ) (hM : 9 ≤ M) (μ A : YoungDiagram)
    (hc : μ.card = A.card) (hn : (staircase M).card ≤ μ.card)
    (hμ : colPrefix μ 4 ≤ 2*M-2)
    (hparts : 2*M-5 ≤ A.colLen 0) (hmax : A.rowLen 0 ≤ M+1)
    (hfour : 2 ≤ A.rowLen 3) : Dominates μ A := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
