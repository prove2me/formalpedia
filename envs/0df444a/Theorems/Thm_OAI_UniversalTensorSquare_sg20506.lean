-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg20506
-- name    : OAI.UniversalTensorSquare.sg20506
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:51:12.754986+00:00
-- url     : https://prove2.me/theorems/ae3dcf4f-3c19-4301-bad1-62e53295559d
-- title:
--   OAI.UniversalTensorSquare.sg20506: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg20506` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg20506 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,2,2,2,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_146All`, `OAI.UniversalTensorSquare.degreeTree62_152All`, `OAI.UniversalTensorSquare.degreeTree62_163All`, `OAI.UniversalTensorSquare.degreeTree62_165All`, `OAI.UniversalTensorSquare.degreeTree62_166All`, `OAI.UniversalTensorSquare.degreeTree62_168All`, `OAI.UniversalTensorSquare.degreeTree62_174All`, `OAI.UniversalTensorSquare.degreeTree62_183All`, `OAI.UniversalTensorSquare.degreeTree62_193All`, `OAI.UniversalTensorSquare.degreeTree62_199All`, `OAI.UniversalTensorSquare.degreeTree62_207All`, `OAI.UniversalTensorSquare.degreeTree62_209All`, `OAI.UniversalTensorSquare.degreeTree62_210All`, `OAI.UniversalTensorSquare.degreeTree62_212All`, `OAI.UniversalTensorSquare.degreeTree62_220All`, `OAI.UniversalTensorSquare.degreeTree62_221All`, `OAI.UniversalTensorSquare.degreeTree62_225All`, `OAI.UniversalTensorSquare.degreeTree62_226All`, `OAI.UniversalTensorSquare.degreeTree62_449All`, `OAI.UniversalTensorSquare.degreeTree62_475All`, `OAI.UniversalTensorSquare.degreeTree62_562All`, `OAI.UniversalTensorSquare.degreeTree62_574All`, `OAI.UniversalTensorSquare.degreeTree62_621All`, `OAI.UniversalTensorSquare.degreeTree62_634All`, `OAI.UniversalTensorSquare.degreeTree62_645All`, `OAI.UniversalTensorSquare.degreeTree62_648All`, `OAI.UniversalTensorSquare.degreeTree62_662All`, `OAI.UniversalTensorSquare.degreeTree62_664All`, `OAI.UniversalTensorSquare.degreeTree62_677All`, `OAI.UniversalTensorSquare.degreeTree62_678All`, `OAI.UniversalTensorSquare.degreeTree62_679All`, `OAI.UniversalTensorSquare.degreeTree62_685All`, `OAI.UniversalTensorSquare.degreeTree62_695All`, `OAI.UniversalTensorSquare.degreeTree62_707All`, `OAI.UniversalTensorSquare.degreeTree62_709All`, `OAI.UniversalTensorSquare.degreeTree62_713All`, `OAI.UniversalTensorSquare.degreeTree62_714All`, `OAI.UniversalTensorSquare.degreeTree62_716All`, `OAI.UniversalTensorSquare.degreeTree62_717All`, `OAI.UniversalTensorSquare.degreeTree62_719All`, `OAI.UniversalTensorSquare.degreeTree62_733All`, `OAI.UniversalTensorSquare.degreeTree62_736All`, `OAI.UniversalTensorSquare.degreeTree62_739All`, `OAI.UniversalTensorSquare.degreeTree62_742All`, `OAI.UniversalTensorSquare.degreeTree62_821All`, `OAI.UniversalTensorSquare.degreeTree62_826All`, `OAI.UniversalTensorSquare.degreeTree62_843All`, `OAI.UniversalTensorSquare.degreeTree62_85All`, `OAI.UniversalTensorSquare.degreeTree62_871All`, `OAI.UniversalTensorSquare.degreeTree62_872All`, `OAI.UniversalTensorSquare.degreeTree62_887All`, `OAI.UniversalTensorSquare.degreeTree62_898All`, `OAI.UniversalTensorSquare.degreeTree62_910All`, `OAI.UniversalTensorSquare.degreeTree62_912All`, `OAI.UniversalTensorSquare.degreeTree62_913All`, `OAI.UniversalTensorSquare.degreeTree62_91All`, `OAI.UniversalTensorSquare.degreeTree62_924All`, `OAI.UniversalTensorSquare.degreeTree62_931All`, `OAI.UniversalTensorSquare.degreeTree62_937All`, `OAI.UniversalTensorSquare.degreeTree62_942All`, `OAI.UniversalTensorSquare.degreeTree62_971All`, `OAI.UniversalTensorSquare.degreeTree62_973All`, `OAI.UniversalTensorSquare.degreeTree62_974All`, `OAI.UniversalTensorSquare.degreeTree62_975All`, `OAI.UniversalTensorSquare.degreeTree62_981All`, `OAI.UniversalTensorSquare.degreeTree62_982All`, `OAI.UniversalTensorSquare.degreeTree62_999All`, `OAI.UniversalTensorSquare.sg32178`, `OAI.UniversalTensorSquare.sg32191`, `OAI.UniversalTensorSquare.sg32237`, `OAI.UniversalTensorSquare.sg32916`, `OAI.UniversalTensorSquare.sg33057`, `OAI.UniversalTensorSquare.sg33639`, `OAI.UniversalTensorSquare.sg33711`, `OAI.UniversalTensorSquare.sg33766`, `OAI.UniversalTensorSquare.sg33933`, `OAI.UniversalTensorSquare.sg34036`, `OAI.UniversalTensorSquare.sg34049`, `OAI.UniversalTensorSquare.sg34131`, `OAI.UniversalTensorSquare.sg37052`, `OAI.UniversalTensorSquare.sg38145`, `OAI.UniversalTensorSquare.sg38241`, `OAI.UniversalTensorSquare.sg38361`, `OAI.UniversalTensorSquare.sg38514`, `OAI.UniversalTensorSquare.sg38594`, `OAI.UniversalTensorSquare.sg38627`, `OAI.UniversalTensorSquare.sg38693`, `OAI.UniversalTensorSquare.sg38724`, `OAI.UniversalTensorSquare.sg38751`, `OAI.UniversalTensorSquare.sg38776`, `OAI.UniversalTensorSquare.sg38846`, `OAI.UniversalTensorSquare.sg39404`, `OAI.UniversalTensorSquare.sg39648`, `OAI.UniversalTensorSquare.sg39756`, `OAI.UniversalTensorSquare.sg40169`, `OAI.UniversalTensorSquare.sg40219`, `OAI.UniversalTensorSquare.sg41178`, `OAI.UniversalTensorSquare.sg41716`, `OAI.UniversalTensorSquare.sg41756`, `OAI.UniversalTensorSquare.sg41776`, `OAI.UniversalTensorSquare.sg41810`, `OAI.UniversalTensorSquare.sg41837`, `OAI.UniversalTensorSquare.sg41910`, `OAI.UniversalTensorSquare.sg41942`, `OAI.UniversalTensorSquare.sg41957`, `OAI.UniversalTensorSquare.sg41969`, `OAI.UniversalTensorSquare.sg42005`, `OAI.UniversalTensorSquare.sg42025`, `OAI.UniversalTensorSquare.sg42067`, `OAI.UniversalTensorSquare.sg42167`, `OAI.UniversalTensorSquare.sg42229`, `OAI.UniversalTensorSquare.sg42257`, `OAI.UniversalTensorSquare.sg42297`, `OAI.UniversalTensorSquare.sg42308`, `OAI.UniversalTensorSquare.sg42338`, `OAI.UniversalTensorSquare.sg42348`, `OAI.UniversalTensorSquare.sg42380`, `OAI.UniversalTensorSquare.sg42414`, `OAI.UniversalTensorSquare.sg42444`, `OAI.UniversalTensorSquare.sg42454`, `OAI.UniversalTensorSquare.sg42483`, `OAI.UniversalTensorSquare.sg42491`, `OAI.UniversalTensorSquare.sg42498`, `OAI.UniversalTensorSquare.sg42529`, `OAI.UniversalTensorSquare.sg42535`, `OAI.UniversalTensorSquare.sg42580`, `OAI.UniversalTensorSquare.sg42603`, `OAI.UniversalTensorSquare.sg42627`, `OAI.UniversalTensorSquare.sg42639`, `OAI.UniversalTensorSquare.sg42657`, `OAI.UniversalTensorSquare.sg42670`, `OAI.UniversalTensorSquare.sg42678`, `OAI.UniversalTensorSquare.sg42685`, `OAI.UniversalTensorSquare.sg42689`, `OAI.UniversalTensorSquare.sg42701`, `OAI.UniversalTensorSquare.sg42735`, `OAI.UniversalTensorSquare.sg42752`, `OAI.UniversalTensorSquare.sg42761`, `OAI.UniversalTensorSquare.sg42764`, `OAI.UniversalTensorSquare.sg42899`, `OAI.UniversalTensorSquare.sg42910`, `OAI.UniversalTensorSquare.sg43023`, `OAI.UniversalTensorSquare.sg43052`, `OAI.UniversalTensorSquare.sg43067`, `OAI.UniversalTensorSquare.sg43076`, `OAI.UniversalTensorSquare.sg43099`, `OAI.UniversalTensorSquare.sg43110`, `OAI.UniversalTensorSquare.sg43114` and `OAI.UniversalTensorSquare.sg43129` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean (declaration OAI.UniversalTensorSquare.sg20506)

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

lemma sg20506 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,2,2,2,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
