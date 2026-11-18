-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg451
-- name    : OAI.UniversalTensorSquare.sg451
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T22:28:28.509371+00:00
-- url     : https://prove2.me/theorems/80978270-a564-4f63-9040-41ac818d2edc
-- title:
--   OAI.UniversalTensorSquare.sg451: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg451` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg451 : RowSquare [3,1,1,1,1,1,1] [6,3]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_122All`, `OAI.UniversalTensorSquare.degreeTree62_236All`, `OAI.UniversalTensorSquare.degreeTree62_255All`, `OAI.UniversalTensorSquare.sg24276`, `OAI.UniversalTensorSquare.sg24642`, `OAI.UniversalTensorSquare.sg24936`, `OAI.UniversalTensorSquare.sg25234`, `OAI.UniversalTensorSquare.sg25281`, `OAI.UniversalTensorSquare.sg26896`, `OAI.UniversalTensorSquare.sg2707`, `OAI.UniversalTensorSquare.sg32067`, `OAI.UniversalTensorSquare.sg32167`, `OAI.UniversalTensorSquare.sg32286`, `OAI.UniversalTensorSquare.sg33249`, `OAI.UniversalTensorSquare.sg33456`, `OAI.UniversalTensorSquare.sg34128`, `OAI.UniversalTensorSquare.sg34446`, `OAI.UniversalTensorSquare.sg34471`, `OAI.UniversalTensorSquare.sg34716`, `OAI.UniversalTensorSquare.sg34743`, `OAI.UniversalTensorSquare.sg34801`, `OAI.UniversalTensorSquare.sg34862`, `OAI.UniversalTensorSquare.sg34912`, `OAI.UniversalTensorSquare.sg34971`, `OAI.UniversalTensorSquare.sg35019`, `OAI.UniversalTensorSquare.sg35124`, `OAI.UniversalTensorSquare.sg35150`, `OAI.UniversalTensorSquare.sg35182`, `OAI.UniversalTensorSquare.sg35265`, `OAI.UniversalTensorSquare.sg35275`, `OAI.UniversalTensorSquare.sg35404`, `OAI.UniversalTensorSquare.sg35607`, `OAI.UniversalTensorSquare.sg35728`, `OAI.UniversalTensorSquare.sg35783`, `OAI.UniversalTensorSquare.sg35930`, `OAI.UniversalTensorSquare.sg36207`, `OAI.UniversalTensorSquare.sg36232`, `OAI.UniversalTensorSquare.sg36300`, `OAI.UniversalTensorSquare.sg36738`, `OAI.UniversalTensorSquare.sg36786`, `OAI.UniversalTensorSquare.sg36810`, `OAI.UniversalTensorSquare.sg37941`, `OAI.UniversalTensorSquare.sg40631` and `OAI.UniversalTensorSquare.sg40924` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean (declaration OAI.UniversalTensorSquare.sg451)

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

lemma sg451 : RowSquare [3,1,1,1,1,1,1] [6,3] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
