-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg445
-- name    : OAI.UniversalTensorSquare.sg445
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:15:47.29873+00:00
-- url     : https://prove2.me/theorems/286e9ae9-81d9-4bfb-9392-793ac021dd04
-- title:
--   OAI.UniversalTensorSquare.sg445: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg445` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg445 : RowSquare [2,2,2,1,1,1] [9]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_348All`, `OAI.UniversalTensorSquare.degreeTree43_365All`, `OAI.UniversalTensorSquare.sg23254`, `OAI.UniversalTensorSquare.sg23261`, `OAI.UniversalTensorSquare.sg23266`, `OAI.UniversalTensorSquare.sg23283`, `OAI.UniversalTensorSquare.sg23291`, `OAI.UniversalTensorSquare.sg23297`, `OAI.UniversalTensorSquare.sg23302`, `OAI.UniversalTensorSquare.sg23316`, `OAI.UniversalTensorSquare.sg23322`, `OAI.UniversalTensorSquare.sg23336`, `OAI.UniversalTensorSquare.sg27667`, `OAI.UniversalTensorSquare.sg27670`, `OAI.UniversalTensorSquare.sg27729`, `OAI.UniversalTensorSquare.sg27733`, `OAI.UniversalTensorSquare.sg27734`, `OAI.UniversalTensorSquare.sg27737`, `OAI.UniversalTensorSquare.sg27781`, `OAI.UniversalTensorSquare.sg27786`, `OAI.UniversalTensorSquare.sg27822`, `OAI.UniversalTensorSquare.sg27828`, `OAI.UniversalTensorSquare.sg27850`, `OAI.UniversalTensorSquare.sg27857`, `OAI.UniversalTensorSquare.sg27963`, `OAI.UniversalTensorSquare.sg27969`, `OAI.UniversalTensorSquare.sg27972`, `OAI.UniversalTensorSquare.sg27973`, `OAI.UniversalTensorSquare.sg28013`, `OAI.UniversalTensorSquare.sg28020`, `OAI.UniversalTensorSquare.sg28024`, `OAI.UniversalTensorSquare.sg28025`, `OAI.UniversalTensorSquare.sg28051`, `OAI.UniversalTensorSquare.sg28059`, `OAI.UniversalTensorSquare.sg28084`, `OAI.UniversalTensorSquare.sg28090`, `OAI.UniversalTensorSquare.sg28091`, `OAI.UniversalTensorSquare.sg28183`, `OAI.UniversalTensorSquare.sg28220`, `OAI.UniversalTensorSquare.sg28243`, `OAI.UniversalTensorSquare.sg28311`, `OAI.UniversalTensorSquare.sg28332`, `OAI.UniversalTensorSquare.sg28375`, `OAI.UniversalTensorSquare.sg28464`, `OAI.UniversalTensorSquare.sg28472`, `OAI.UniversalTensorSquare.sg28512`, `OAI.UniversalTensorSquare.sg28522`, `OAI.UniversalTensorSquare.sg28547`, `OAI.UniversalTensorSquare.sg28559`, `OAI.UniversalTensorSquare.sg28582`, `OAI.UniversalTensorSquare.sg28666`, `OAI.UniversalTensorSquare.sg28700`, `OAI.UniversalTensorSquare.sg28721`, `OAI.UniversalTensorSquare.sg28779`, `OAI.UniversalTensorSquare.sg28797`, `OAI.UniversalTensorSquare.sg28832`, `OAI.UniversalTensorSquare.sg31811`, `OAI.UniversalTensorSquare.sg31825`, `OAI.UniversalTensorSquare.sg31831`, `OAI.UniversalTensorSquare.sg31850`, `OAI.UniversalTensorSquare.sg31857`, `OAI.UniversalTensorSquare.sg31862`, `OAI.UniversalTensorSquare.sg31863`, `OAI.UniversalTensorSquare.sg31870`, `OAI.UniversalTensorSquare.sg31873`, `OAI.UniversalTensorSquare.sg31877`, `OAI.UniversalTensorSquare.sg31880`, `OAI.UniversalTensorSquare.sg31883`, `OAI.UniversalTensorSquare.sg31884`, `OAI.UniversalTensorSquare.sg31898`, `OAI.UniversalTensorSquare.sg31902`, `OAI.UniversalTensorSquare.sg31904`, `OAI.UniversalTensorSquare.sg31906`, `OAI.UniversalTensorSquare.sg31911`, `OAI.UniversalTensorSquare.sg32448` and `OAI.UniversalTensorSquare.sg32680` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg445)

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

lemma sg445 : RowSquare [2,2,2,1,1,1] [9] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
