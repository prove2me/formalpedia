-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_candidate_cone
-- name    : OAI.UniversalTensorSquare.candidate_cone
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T17:10:18.011745+00:00
-- url     : https://prove2.me/theorems/83f78c36-fa74-4555-9268-9773abc4ee4a
-- title:
--   OAI.UniversalTensorSquare.candidate_cone: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.candidate_cone` of [lean/OAI/RepresentationTheory/UniversalSquare/Support/NumericalSupport.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/NumericalSupport.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Balance Saxl.Columns`):
--
--   ```lean
--   lemma candidate_cone {n M b δ : ℕ} (hM : 4 ≤ M)
--       (hn : (candidate M b δ).card = n) (p : PackingPlan) (q : List ℕ)
--       (hq : GoodRows q) (hqn : q.sum = n)
--       (hv : p.Valid (M+b+δ)) (hb : BandsValid p.bands)
--       (hc : p.columns.Perm ([M+b+δ,M-1+b] ++
--         (List.range' 3 (M-4)).reverse ++ List.replicate (b+1) 2 ++ List.replicate (1+δ) 1))
--       (hp : p.parts.Perm q) (μ : YoungDiagram) (hμ : μ.card = n)
--       (hd : RowsDom μ.rowLens q) : SquareOccurs (candidate M b δ) μ
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Balance.BandsValid` (definitions bundle `OAIQ259US000` of this split); `OAI.UniversalTensorSquare.GoodRows`, `OAI.UniversalTensorSquare.RowsDom`, `OAI.Saxl.Balance.PackingPlan`, `OAI.Saxl.Balance.PackingPlan.Valid`, `OAI.Saxl.Balance.PackingPlan.bands`, `OAI.Saxl.Balance.PackingPlan.columns` and `OAI.Saxl.Balance.PackingPlan.parts` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.SquareOccurs` and `OAI.UniversalTensorSquare.candidate` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.universal_partition_exceptional` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/NumericalSupport.lean (declaration OAI.UniversalTensorSquare.candidate_cone)

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
open Saxl Saxl.Balance Saxl.Columns

lemma candidate_cone {n M b δ : ℕ} (hM : 4 ≤ M)
    (hn : (candidate M b δ).card = n) (p : PackingPlan) (q : List ℕ)
    (hq : GoodRows q) (hqn : q.sum = n)
    (hv : p.Valid (M+b+δ)) (hb : BandsValid p.bands)
    (hc : p.columns.Perm ([M+b+δ,M-1+b] ++
      (List.range' 3 (M-4)).reverse ++ List.replicate (b+1) 2 ++ List.replicate (1+δ) 1))
    (hp : p.parts.Perm q) (μ : YoungDiagram) (hμ : μ.card = n)
    (hd : RowsDom μ.rowLens q) : SquareOccurs (candidate M b δ) μ := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
