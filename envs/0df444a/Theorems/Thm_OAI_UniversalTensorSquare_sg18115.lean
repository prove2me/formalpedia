-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg18115
-- name    : OAI.UniversalTensorSquare.sg18115
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:38:41.652226+00:00
-- url     : https://prove2.me/theorems/3631476d-ea52-487e-a90d-0b146f950ba2
-- title:
--   OAI.UniversalTensorSquare.sg18115: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg18115` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes43.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes43.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg18115 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,4,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_104All`, `OAI.UniversalTensorSquare.degreeTree62_12All`, `OAI.UniversalTensorSquare.degreeTree62_13All`, `OAI.UniversalTensorSquare.degreeTree62_226All`, `OAI.UniversalTensorSquare.degreeTree62_235All`, `OAI.UniversalTensorSquare.degreeTree62_293All`, `OAI.UniversalTensorSquare.degreeTree62_2All`, `OAI.UniversalTensorSquare.degreeTree62_326All`, `OAI.UniversalTensorSquare.degreeTree62_394All`, `OAI.UniversalTensorSquare.degreeTree62_3All`, `OAI.UniversalTensorSquare.degreeTree62_42All`, `OAI.UniversalTensorSquare.degreeTree62_475All`, `OAI.UniversalTensorSquare.degreeTree62_515All`, `OAI.UniversalTensorSquare.degreeTree62_518All`, `OAI.UniversalTensorSquare.degreeTree62_614All`, `OAI.UniversalTensorSquare.degreeTree62_713All`, `OAI.UniversalTensorSquare.degreeTree62_75All`, `OAI.UniversalTensorSquare.degreeTree62_8All`, `OAI.UniversalTensorSquare.sg32038`, `OAI.UniversalTensorSquare.sg32092`, `OAI.UniversalTensorSquare.sg32131`, `OAI.UniversalTensorSquare.sg32148`, `OAI.UniversalTensorSquare.sg32250`, `OAI.UniversalTensorSquare.sg32593`, `OAI.UniversalTensorSquare.sg32643`, `OAI.UniversalTensorSquare.sg32676`, `OAI.UniversalTensorSquare.sg32699`, `OAI.UniversalTensorSquare.sg32718`, `OAI.UniversalTensorSquare.sg32721`, `OAI.UniversalTensorSquare.sg32738`, `OAI.UniversalTensorSquare.sg32740`, `OAI.UniversalTensorSquare.sg32812`, `OAI.UniversalTensorSquare.sg32875`, `OAI.UniversalTensorSquare.sg32947`, `OAI.UniversalTensorSquare.sg33052`, `OAI.UniversalTensorSquare.sg33084`, `OAI.UniversalTensorSquare.sg33396`, `OAI.UniversalTensorSquare.sg33419`, `OAI.UniversalTensorSquare.sg33611`, `OAI.UniversalTensorSquare.sg33615`, `OAI.UniversalTensorSquare.sg33798`, `OAI.UniversalTensorSquare.sg33962`, `OAI.UniversalTensorSquare.sg33995`, `OAI.UniversalTensorSquare.sg34018`, `OAI.UniversalTensorSquare.sg34274`, `OAI.UniversalTensorSquare.sg34556`, `OAI.UniversalTensorSquare.sg34579`, `OAI.UniversalTensorSquare.sg34604`, `OAI.UniversalTensorSquare.sg34637`, `OAI.UniversalTensorSquare.sg35431`, `OAI.UniversalTensorSquare.sg35446`, `OAI.UniversalTensorSquare.sg35456`, `OAI.UniversalTensorSquare.sg36354`, `OAI.UniversalTensorSquare.sg37069`, `OAI.UniversalTensorSquare.sg37511`, `OAI.UniversalTensorSquare.sg38379`, `OAI.UniversalTensorSquare.sg38907`, `OAI.UniversalTensorSquare.sg38920` and `OAI.UniversalTensorSquare.sg39534` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes43.lean (declaration OAI.UniversalTensorSquare.sg18115)

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
open Saxl Saxl.Columns Saxl.Balance

lemma sg18115 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,4,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
