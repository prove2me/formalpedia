-- Prove2me | Theorems.Thm_OAI_Saxl_Balance_WordPacking_neighbor
-- name    : OAI.Saxl.Balance.WordPacking.neighbor
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T18:15:27.5192+00:00
-- url     : https://prove2.me/theorems/dda1c94a-5e78-4bcf-9dbf-c0e1acb35a2e
-- title:
--   OAI.Saxl.Balance.WordPacking.neighbor: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Saxl.Balance.WordPacking.neighbor` of [lean/OAI/RepresentationTheory/UniversalSquare/Balance/WordPackingGeometry.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Balance/WordPackingGeometry.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Saxl.Balance`, with `open FlagColumns Columns`):
--
--   ```lean
--   theorem WordPacking.neighbor {r d : ℕ} (hr : 0 < r) (hd : r+1 ≤ d)
--       {ps : List ℕ} (hsum : ps.sum = 2*r+1) (hlen : ps.length ≤ 4)
--       (k : ℕ) (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
--       (he : ∀ a, (A a ∧ label a = k) ↔ output a ∈ Set.Icc r (r+1)) :
--       Nonempty (WordPacking [r+1,r] ps d A label {k})
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Balance.output` (definitions bundle `OAIQ259US000` of this split); `OAI.Saxl.Balance.WordPacking` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.Saxl.Balance.PackingPlan.realize` and `OAI.Saxl.Balance.balancePacking` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Balance/WordPackingGeometry.lean (declaration OAI.Saxl.Balance.WordPacking.neighbor)

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

theorem WordPacking.neighbor {r d : ℕ} (hr : 0 < r) (hd : r+1 ≤ d)
    {ps : List ℕ} (hsum : ps.sum = 2*r+1) (hlen : ps.length ≤ 4)
    (k : ℕ) (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (he : ∀ a, (A a ∧ label a = k) ↔ output a ∈ Set.Icc r (r+1)) :
    Nonempty (WordPacking [r+1,r] ps d A label {k}) := by
  sorry

end Saxl.Balance
end
end

end OAI
end
