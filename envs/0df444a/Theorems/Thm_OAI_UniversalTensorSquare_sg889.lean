-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg889
-- name    : OAI.UniversalTensorSquare.sg889
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T23:52:45.345585+00:00
-- url     : https://prove2.me/theorems/aa477456-b30e-4b4d-b196-99ad7e2dda31
-- title:
--   OAI.UniversalTensorSquare.sg889: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg889` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg889 : RowSquare [5,1,1,1,1,1] [2,2,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_85All`, `OAI.UniversalTensorSquare.degreeTree62_733All`, `OAI.UniversalTensorSquare.degreeTree62_80All`, `OAI.UniversalTensorSquare.degreeTree62_917All`, `OAI.UniversalTensorSquare.degreeTree62_955All`, `OAI.UniversalTensorSquare.degreeTree62_985All`, `OAI.UniversalTensorSquare.degreeTree62_989All`, `OAI.UniversalTensorSquare.sg10090`, `OAI.UniversalTensorSquare.sg10211`, `OAI.UniversalTensorSquare.sg10215`, `OAI.UniversalTensorSquare.sg10219`, `OAI.UniversalTensorSquare.sg10221`, `OAI.UniversalTensorSquare.sg10288`, `OAI.UniversalTensorSquare.sg10295`, `OAI.UniversalTensorSquare.sg11496`, `OAI.UniversalTensorSquare.sg1334`, `OAI.UniversalTensorSquare.sg15644`, `OAI.UniversalTensorSquare.sg17299`, `OAI.UniversalTensorSquare.sg19623`, `OAI.UniversalTensorSquare.sg19624`, `OAI.UniversalTensorSquare.sg20508`, `OAI.UniversalTensorSquare.sg20790`, `OAI.UniversalTensorSquare.sg21909`, `OAI.UniversalTensorSquare.sg21913`, `OAI.UniversalTensorSquare.sg21918`, `OAI.UniversalTensorSquare.sg21923`, `OAI.UniversalTensorSquare.sg21930`, `OAI.UniversalTensorSquare.sg21936`, `OAI.UniversalTensorSquare.sg21942`, `OAI.UniversalTensorSquare.sg21992`, `OAI.UniversalTensorSquare.sg22006`, `OAI.UniversalTensorSquare.sg22342`, `OAI.UniversalTensorSquare.sg22351`, `OAI.UniversalTensorSquare.sg22355`, `OAI.UniversalTensorSquare.sg22363`, `OAI.UniversalTensorSquare.sg22370`, `OAI.UniversalTensorSquare.sg22374`, `OAI.UniversalTensorSquare.sg2274`, `OAI.UniversalTensorSquare.sg24126`, `OAI.UniversalTensorSquare.sg24157`, `OAI.UniversalTensorSquare.sg24160`, `OAI.UniversalTensorSquare.sg24169`, `OAI.UniversalTensorSquare.sg24174`, `OAI.UniversalTensorSquare.sg24192`, `OAI.UniversalTensorSquare.sg24200`, `OAI.UniversalTensorSquare.sg24565`, `OAI.UniversalTensorSquare.sg24574`, `OAI.UniversalTensorSquare.sg24576`, `OAI.UniversalTensorSquare.sg25493`, `OAI.UniversalTensorSquare.sg25508`, `OAI.UniversalTensorSquare.sg25716`, `OAI.UniversalTensorSquare.sg25730`, `OAI.UniversalTensorSquare.sg25733`, `OAI.UniversalTensorSquare.sg25852`, `OAI.UniversalTensorSquare.sg25859`, `OAI.UniversalTensorSquare.sg25875`, `OAI.UniversalTensorSquare.sg25880`, `OAI.UniversalTensorSquare.sg25896`, `OAI.UniversalTensorSquare.sg26232`, `OAI.UniversalTensorSquare.sg26260`, `OAI.UniversalTensorSquare.sg26273`, `OAI.UniversalTensorSquare.sg26276`, `OAI.UniversalTensorSquare.sg26284`, `OAI.UniversalTensorSquare.sg26289`, `OAI.UniversalTensorSquare.sg26504`, `OAI.UniversalTensorSquare.sg26517`, `OAI.UniversalTensorSquare.sg26522`, `OAI.UniversalTensorSquare.sg26533`, `OAI.UniversalTensorSquare.sg26614`, `OAI.UniversalTensorSquare.sg26759`, `OAI.UniversalTensorSquare.sg26765`, `OAI.UniversalTensorSquare.sg2721`, `OAI.UniversalTensorSquare.sg27265`, `OAI.UniversalTensorSquare.sg27268`, `OAI.UniversalTensorSquare.sg2731`, `OAI.UniversalTensorSquare.sg27422`, `OAI.UniversalTensorSquare.sg27471`, `OAI.UniversalTensorSquare.sg27731`, `OAI.UniversalTensorSquare.sg27971`, `OAI.UniversalTensorSquare.sg28714`, `OAI.UniversalTensorSquare.sg28824`, `OAI.UniversalTensorSquare.sg28851`, `OAI.UniversalTensorSquare.sg28853`, `OAI.UniversalTensorSquare.sg29332`, `OAI.UniversalTensorSquare.sg29505`, `OAI.UniversalTensorSquare.sg29507`, `OAI.UniversalTensorSquare.sg29522`, `OAI.UniversalTensorSquare.sg29528`, `OAI.UniversalTensorSquare.sg29725`, `OAI.UniversalTensorSquare.sg29737`, `OAI.UniversalTensorSquare.sg29740`, `OAI.UniversalTensorSquare.sg29749`, `OAI.UniversalTensorSquare.sg29756`, `OAI.UniversalTensorSquare.sg30127`, `OAI.UniversalTensorSquare.sg30271`, `OAI.UniversalTensorSquare.sg30277`, `OAI.UniversalTensorSquare.sg30289`, `OAI.UniversalTensorSquare.sg30292`, `OAI.UniversalTensorSquare.sg30446`, `OAI.UniversalTensorSquare.sg31399`, `OAI.UniversalTensorSquare.sg32183`, `OAI.UniversalTensorSquare.sg32185`, `OAI.UniversalTensorSquare.sg32194`, `OAI.UniversalTensorSquare.sg32240`, `OAI.UniversalTensorSquare.sg32249`, `OAI.UniversalTensorSquare.sg32255`, `OAI.UniversalTensorSquare.sg32910`, `OAI.UniversalTensorSquare.sg32972`, `OAI.UniversalTensorSquare.sg32981`, `OAI.UniversalTensorSquare.sg33023`, `OAI.UniversalTensorSquare.sg33060`, `OAI.UniversalTensorSquare.sg33644`, `OAI.UniversalTensorSquare.sg33646`, `OAI.UniversalTensorSquare.sg33655`, `OAI.UniversalTensorSquare.sg33663`, `OAI.UniversalTensorSquare.sg33727`, `OAI.UniversalTensorSquare.sg3553`, `OAI.UniversalTensorSquare.sg36376`, `OAI.UniversalTensorSquare.sg36378`, `OAI.UniversalTensorSquare.sg36391`, `OAI.UniversalTensorSquare.sg36393`, `OAI.UniversalTensorSquare.sg36566`, `OAI.UniversalTensorSquare.sg36667`, `OAI.UniversalTensorSquare.sg4358`, `OAI.UniversalTensorSquare.sg4376`, `OAI.UniversalTensorSquare.sg4846`, `OAI.UniversalTensorSquare.sg6394`, `OAI.UniversalTensorSquare.sg6401`, `OAI.UniversalTensorSquare.sg6418`, `OAI.UniversalTensorSquare.sg7307`, `OAI.UniversalTensorSquare.sg7341`, `OAI.UniversalTensorSquare.sg7347`, `OAI.UniversalTensorSquare.sg7528`, `OAI.UniversalTensorSquare.sg8707` and `OAI.UniversalTensorSquare.sg8718` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean (declaration OAI.UniversalTensorSquare.sg889)

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

lemma sg889 : RowSquare [5,1,1,1,1,1] [2,2,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
