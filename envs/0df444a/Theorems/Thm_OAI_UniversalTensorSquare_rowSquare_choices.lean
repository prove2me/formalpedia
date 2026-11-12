-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices
-- name    : OAI.UniversalTensorSquare.rowSquare_choices
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T20:23:37.508175+00:00
-- url     : https://prove2.me/theorems/ec12cbc9-99f5-4b10-967a-c701edc425a3
-- title:
--   OAI.UniversalTensorSquare.rowSquare_choices: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.rowSquare_choices` of [lean/OAI/RepresentationTheory/UniversalSquare/Contraction/ChoiceContractions.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Contraction/ChoiceContractions.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open scoped BigOperators`, `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma rowSquare_choices {n : ℕ} {p q cs ts : List ℕ}
--       (hp : GoodRows p) (hq : GoodRows q) (hcs : GoodRows cs) (hts : GoodRows ts)
--       (he : cs = transposeRows p ∨ cs = p) (ht : ts = transposeRows q)
--       (hn : cs.sum = n) (hn' : ts.sum = n)
--       (eb : Fin n ≃ Fin cs.sum) (et : Fin n ≃ Fin ts.sum)
--       (flag : Finset (ℕ × ℕ × ℕ)) (ch : EdgeChoices)
--       (hcert : solveChoices ch (.full ts) (.full cs) (.full cs)
--         (certificateEdges cs cs ts (finCongr hn.symm) eb et) flag ≠ 0) : RowSquare p q
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.GoodRows`, `OAI.UniversalTensorSquare.transposeRows`, `OAI.Saxl.Columns.EdgeChoices` and `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveChoices` (definitions bundle `OAIQ259US006` of this split); `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.smallSupport11_0`, `OAI.UniversalTensorSquare.smallSupport11_17`, `OAI.UniversalTensorSquare.smallSupport11_18`, `OAI.UniversalTensorSquare.smallSupport11_23`, `OAI.UniversalTensorSquare.smallSupport11_25`, `OAI.UniversalTensorSquare.smallSupport11_27`, `OAI.UniversalTensorSquare.smallSupport11_4`, `OAI.UniversalTensorSquare.smallSupport11_5`, `OAI.UniversalTensorSquare.smallSupport11_6`, `OAI.UniversalTensorSquare.smallSupport11_7`, `OAI.UniversalTensorSquare.smallSupport11_9`, `OAI.UniversalTensorSquare.smallSupport13_0`, `OAI.UniversalTensorSquare.smallSupport13_1`, `OAI.UniversalTensorSquare.smallSupport13_10`, `OAI.UniversalTensorSquare.smallSupport13_11`, `OAI.UniversalTensorSquare.smallSupport13_12`, `OAI.UniversalTensorSquare.smallSupport13_13`, `OAI.UniversalTensorSquare.smallSupport13_14`, `OAI.UniversalTensorSquare.smallSupport13_15`, `OAI.UniversalTensorSquare.smallSupport13_16`, `OAI.UniversalTensorSquare.smallSupport13_17`, `OAI.UniversalTensorSquare.smallSupport13_18`, `OAI.UniversalTensorSquare.smallSupport13_19`, `OAI.UniversalTensorSquare.smallSupport13_2`, `OAI.UniversalTensorSquare.smallSupport13_24`, `OAI.UniversalTensorSquare.smallSupport13_26`, `OAI.UniversalTensorSquare.smallSupport13_27`, `OAI.UniversalTensorSquare.smallSupport13_28`, `OAI.UniversalTensorSquare.smallSupport13_29`, `OAI.UniversalTensorSquare.smallSupport13_3`, `OAI.UniversalTensorSquare.smallSupport13_30`, `OAI.UniversalTensorSquare.smallSupport13_32`, `OAI.UniversalTensorSquare.smallSupport13_33`, `OAI.UniversalTensorSquare.smallSupport13_34`, `OAI.UniversalTensorSquare.smallSupport13_35`, `OAI.UniversalTensorSquare.smallSupport13_40`, `OAI.UniversalTensorSquare.smallSupport13_43`, `OAI.UniversalTensorSquare.smallSupport13_44`, `OAI.UniversalTensorSquare.smallSupport13_45`, `OAI.UniversalTensorSquare.smallSupport13_47`, `OAI.UniversalTensorSquare.smallSupport13_48`, `OAI.UniversalTensorSquare.smallSupport13_49`, `OAI.UniversalTensorSquare.smallSupport13_50`, `OAI.UniversalTensorSquare.smallSupport13_9`, `OAI.UniversalTensorSquare.smallSupports11` and `OAI.UniversalTensorSquare.smallSupports13` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Contraction/ChoiceContractions.lean (declaration OAI.UniversalTensorSquare.rowSquare_choices)

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped BigOperators

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma rowSquare_choices {n : ℕ} {p q cs ts : List ℕ}
    (hp : GoodRows p) (hq : GoodRows q) (hcs : GoodRows cs) (hts : GoodRows ts)
    (he : cs = transposeRows p ∨ cs = p) (ht : ts = transposeRows q)
    (hn : cs.sum = n) (hn' : ts.sum = n)
    (eb : Fin n ≃ Fin cs.sum) (et : Fin n ≃ Fin ts.sum)
    (flag : Finset (ℕ × ℕ × ℕ)) (ch : EdgeChoices)
    (hcert : solveChoices ch (.full ts) (.full cs) (.full cs)
      (certificateEdges cs cs ts (finCongr hn.symm) eb et) flag ≠ 0) : RowSquare p q := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
