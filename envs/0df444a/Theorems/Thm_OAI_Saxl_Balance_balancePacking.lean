-- Prove2me | Theorems.Thm_OAI_Saxl_Balance_balancePacking
-- name    : OAI.Saxl.Balance.balancePacking
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T18:15:07.680055+00:00
-- url     : https://prove2.me/theorems/27a215ac-f8ba-4622-8ddb-c257bf050d44
-- title:
--   OAI.Saxl.Balance.balancePacking: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Saxl.Balance.balancePacking` of [lean/OAI/RepresentationTheory/UniversalSquare/Balance/BalanceAssembly.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Balance/BalanceAssembly.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Saxl.Balance`, with `open FlagColumns Columns`):
--
--   ```lean
--   theorem balancePacking {M b δ τ ε m : ℕ}
--       (hM : 4 ≤ M) (hδ : δ ≤ 1) (hτ : τ ≤ 1) (hε : ε ≤ 1)
--       (heq : M = 4+τ+ε+2*m) (hshort : τ ≠ 0 → 1 ≤ b) :
--       ∃ (A : Fin ((M+b+δ)*(M+b+δ)) → Prop)
--         (label : Fin ((M+b+δ)*(M+b+δ)) → ℕ) (marks : Finset ℕ),
--         (∀ x y, A x → A y → label x < label y → output x < output y) ∧
--         Nonempty (WordPacking (balanceColumns M b δ τ ε m)
--           (balanceParts M b δ τ ε m) (M+b+δ) A label marks)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Balance.output` (definitions bundle `OAIQ259US000` of this split); `OAI.Saxl.Balance.balanceParts` (definitions bundle `OAIQ259US001` of this split); `OAI.Saxl.Balance.WordPacking` and `OAI.Saxl.Balance.balanceColumns` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.exceptional_pos106`, `OAI.UniversalTensorSquare.exceptional_pos108`, `OAI.UniversalTensorSquare.exceptional_pos110`, `OAI.UniversalTensorSquare.exceptional_pos114`, `OAI.UniversalTensorSquare.exceptional_pos149`, `OAI.UniversalTensorSquare.exceptional_pos71`, `OAI.UniversalTensorSquare.exceptional_pos75`, `OAI.UniversalTensorSquare.exceptional_pos79`, `OAI.UniversalTensorSquare.exceptional_pos81`, `OAI.UniversalTensorSquare.exceptional_pos83`, `OAI.UniversalTensorSquare.exceptional_pos85`, `OAI.UniversalTensorSquare.exceptional_pos87`, `OAI.UniversalTensorSquare.universal_partition_exceptional` and `OAI.UniversalTensorSquares.universal_tensor_square` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Balance/BalanceAssembly.lean (declaration OAI.Saxl.Balance.balancePacking)

import Mathlib
import Definitions.Def_OAIQ259US006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace Saxl.Balance
open FlagColumns Columns

theorem balancePacking {M b δ τ ε m : ℕ}
    (hM : 4 ≤ M) (hδ : δ ≤ 1) (hτ : τ ≤ 1) (hε : ε ≤ 1)
    (heq : M = 4+τ+ε+2*m) (hshort : τ ≠ 0 → 1 ≤ b) :
    ∃ (A : Fin ((M+b+δ)*(M+b+δ)) → Prop)
      (label : Fin ((M+b+δ)*(M+b+δ)) → ℕ) (marks : Finset ℕ),
      (∀ x y, A x → A y → label x < label y → output x < output y) ∧
      Nonempty (WordPacking (balanceColumns M b δ τ ε m)
        (balanceParts M b δ τ ε m) (M+b+δ) A label marks) := by
  sorry

end Saxl.Balance
end
end

end OAI
end
