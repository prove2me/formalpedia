-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_balance_kronecker_pos
-- name    : OAI.UniversalTensorSquare.balance_kronecker_pos
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T17:10:10.00267+00:00
-- url     : https://prove2.me/theorems/c2e10c55-3673-41b7-bc7d-e16c1f035d12
-- title:
--   OAI.UniversalTensorSquare.balance_kronecker_pos: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.balance_kronecker_pos` of [lean/OAI/RepresentationTheory/UniversalSquare/Balance/BalanceFour.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Balance/BalanceFour.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Balance Saxl.Columns Saxl.FlagColumns`):
--
--   ```lean
--   theorem balance_kronecker_pos {n M b δ : ℕ} (hM : 9 ≤ M)
--       (hb : b ≤ M-2) (hδ : δ ≤ 1)
--       (t : Tableau n (candidate M b δ)) (μ : YoungDiagram) (s : Tableau n μ)
--       (hμ : colPrefix μ 4 ≤ 2*M-2) : 0 < kronecker t t s
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.colPrefix` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.candidate` (definitions bundle `OAIQ259US007` of this split); `OAI.Saxl.Tableau` and `OAI.Saxl.kronecker` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.balance_kronecker_pos_or_transpose` and `OAI.UniversalTensorSquare.candidate_refined_pos` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Balance/BalanceFour.lean (declaration OAI.UniversalTensorSquare.balance_kronecker_pos)

import Mathlib
import Definitions.Def_UniversalTensorSquares
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
open Saxl Saxl.Balance Saxl.Columns Saxl.FlagColumns

theorem balance_kronecker_pos {n M b δ : ℕ} (hM : 9 ≤ M)
    (hb : b ≤ M-2) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (μ : YoungDiagram) (s : Tableau n μ)
    (hμ : colPrefix μ 4 ≤ 2*M-2) : 0 < kronecker t t s := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
