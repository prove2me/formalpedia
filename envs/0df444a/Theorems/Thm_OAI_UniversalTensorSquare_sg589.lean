-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg589
-- name    : OAI.UniversalTensorSquare.sg589
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T22:47:43.885652+00:00
-- url     : https://prove2.me/theorems/31b0660d-a157-4b77-ad11-0646958100f7
-- title:
--   OAI.UniversalTensorSquare.sg589: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg589` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg589 : RowSquare [5,1,1,1,1] [2,2,2,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_37All`, `OAI.UniversalTensorSquare.degreeTree39_77All`, `OAI.UniversalTensorSquare.degreeTree43_47All`, `OAI.UniversalTensorSquare.degreeTree43_480All`, `OAI.UniversalTensorSquare.degreeTree43_598All`, `OAI.UniversalTensorSquare.degreeTree43_86All`, `OAI.UniversalTensorSquare.degreeTree62_640All`, `OAI.UniversalTensorSquare.degreeTree62_705All`, `OAI.UniversalTensorSquare.sg16293`, `OAI.UniversalTensorSquare.sg16715`, `OAI.UniversalTensorSquare.sg18088`, `OAI.UniversalTensorSquare.sg21699`, `OAI.UniversalTensorSquare.sg21734`, `OAI.UniversalTensorSquare.sg22112`, `OAI.UniversalTensorSquare.sg22822`, `OAI.UniversalTensorSquare.sg23080`, `OAI.UniversalTensorSquare.sg23302`, `OAI.UniversalTensorSquare.sg23498`, `OAI.UniversalTensorSquare.sg23896`, `OAI.UniversalTensorSquare.sg24130`, `OAI.UniversalTensorSquare.sg24131`, `OAI.UniversalTensorSquare.sg24284`, `OAI.UniversalTensorSquare.sg24336`, `OAI.UniversalTensorSquare.sg24370`, `OAI.UniversalTensorSquare.sg24844`, `OAI.UniversalTensorSquare.sg24901`, `OAI.UniversalTensorSquare.sg24918`, `OAI.UniversalTensorSquare.sg24935`, `OAI.UniversalTensorSquare.sg24936`, `OAI.UniversalTensorSquare.sg24937`, `OAI.UniversalTensorSquare.sg25234`, `OAI.UniversalTensorSquare.sg25281`, `OAI.UniversalTensorSquare.sg25283`, `OAI.UniversalTensorSquare.sg25326`, `OAI.UniversalTensorSquare.sg25466`, `OAI.UniversalTensorSquare.sg25565`, `OAI.UniversalTensorSquare.sg25581`, `OAI.UniversalTensorSquare.sg25582`, `OAI.UniversalTensorSquare.sg25806`, `OAI.UniversalTensorSquare.sg25981`, `OAI.UniversalTensorSquare.sg26087`, `OAI.UniversalTensorSquare.sg26088`, `OAI.UniversalTensorSquare.sg26151`, `OAI.UniversalTensorSquare.sg26449`, `OAI.UniversalTensorSquare.sg26632`, `OAI.UniversalTensorSquare.sg26699`, `OAI.UniversalTensorSquare.sg26742`, `OAI.UniversalTensorSquare.sg26887`, `OAI.UniversalTensorSquare.sg26896`, `OAI.UniversalTensorSquare.sg27222`, `OAI.UniversalTensorSquare.sg27398`, `OAI.UniversalTensorSquare.sg28737`, `OAI.UniversalTensorSquare.sg28746`, `OAI.UniversalTensorSquare.sg29025`, `OAI.UniversalTensorSquare.sg29037`, `OAI.UniversalTensorSquare.sg29042`, `OAI.UniversalTensorSquare.sg29043`, `OAI.UniversalTensorSquare.sg29045`, `OAI.UniversalTensorSquare.sg29058`, `OAI.UniversalTensorSquare.sg29060`, `OAI.UniversalTensorSquare.sg29363`, `OAI.UniversalTensorSquare.sg29435`, `OAI.UniversalTensorSquare.sg29438`, `OAI.UniversalTensorSquare.sg29444`, `OAI.UniversalTensorSquare.sg29564`, `OAI.UniversalTensorSquare.sg29609`, `OAI.UniversalTensorSquare.sg29634`, `OAI.UniversalTensorSquare.sg29694`, `OAI.UniversalTensorSquare.sg29825`, `OAI.UniversalTensorSquare.sg29860`, `OAI.UniversalTensorSquare.sg30042`, `OAI.UniversalTensorSquare.sg30203`, `OAI.UniversalTensorSquare.sg30938`, `OAI.UniversalTensorSquare.sg31477`, `OAI.UniversalTensorSquare.sg34639`, `OAI.UniversalTensorSquare.sg34640`, `OAI.UniversalTensorSquare.sg34659`, `OAI.UniversalTensorSquare.sg34747`, `OAI.UniversalTensorSquare.sg34767`, `OAI.UniversalTensorSquare.sg34768`, `OAI.UniversalTensorSquare.sg34769`, `OAI.UniversalTensorSquare.sg34831`, `OAI.UniversalTensorSquare.sg34879`, `OAI.UniversalTensorSquare.sg34882`, `OAI.UniversalTensorSquare.sg34893`, `OAI.UniversalTensorSquare.sg34942`, `OAI.UniversalTensorSquare.sg35030`, `OAI.UniversalTensorSquare.sg35042`, `OAI.UniversalTensorSquare.sg35055`, `OAI.UniversalTensorSquare.sg35081`, `OAI.UniversalTensorSquare.sg35087`, `OAI.UniversalTensorSquare.sg35111`, `OAI.UniversalTensorSquare.sg35232`, `OAI.UniversalTensorSquare.sg3620`, `OAI.UniversalTensorSquare.sg36669`, `OAI.UniversalTensorSquare.sg36753`, `OAI.UniversalTensorSquare.sg36798`, `OAI.UniversalTensorSquare.sg36840`, `OAI.UniversalTensorSquare.sg36844`, `OAI.UniversalTensorSquare.sg37151`, `OAI.UniversalTensorSquare.sg37225`, `OAI.UniversalTensorSquare.sg37226`, `OAI.UniversalTensorSquare.sg37228`, `OAI.UniversalTensorSquare.sg37229`, `OAI.UniversalTensorSquare.sg37231`, `OAI.UniversalTensorSquare.sg37233`, `OAI.UniversalTensorSquare.sg37236`, `OAI.UniversalTensorSquare.sg37240`, `OAI.UniversalTensorSquare.sg37280`, `OAI.UniversalTensorSquare.sg37283`, `OAI.UniversalTensorSquare.sg37307`, `OAI.UniversalTensorSquare.sg37308`, `OAI.UniversalTensorSquare.sg37347`, `OAI.UniversalTensorSquare.sg37511`, `OAI.UniversalTensorSquare.sg38040`, `OAI.UniversalTensorSquare.sg38045`, `OAI.UniversalTensorSquare.sg38047`, `OAI.UniversalTensorSquare.sg38049`, `OAI.UniversalTensorSquare.sg38174`, `OAI.UniversalTensorSquare.sg38195`, `OAI.UniversalTensorSquare.sg38455`, `OAI.UniversalTensorSquare.sg38456`, `OAI.UniversalTensorSquare.sg38458`, `OAI.UniversalTensorSquare.sg38459`, `OAI.UniversalTensorSquare.sg38461`, `OAI.UniversalTensorSquare.sg38463`, `OAI.UniversalTensorSquare.sg38549`, `OAI.UniversalTensorSquare.sg38552`, `OAI.UniversalTensorSquare.sg38591`, `OAI.UniversalTensorSquare.sg38597`, `OAI.UniversalTensorSquare.sg38694`, `OAI.UniversalTensorSquare.sg39247`, `OAI.UniversalTensorSquare.sg39248`, `OAI.UniversalTensorSquare.sg39250`, `OAI.UniversalTensorSquare.sg39251`, `OAI.UniversalTensorSquare.sg39253`, `OAI.UniversalTensorSquare.sg40106`, `OAI.UniversalTensorSquare.sg40107`, `OAI.UniversalTensorSquare.sg40109`, `OAI.UniversalTensorSquare.sg40110`, `OAI.UniversalTensorSquare.sg40649`, `OAI.UniversalTensorSquare.sg41232`, `OAI.UniversalTensorSquare.sg41233`, `OAI.UniversalTensorSquare.sg41235`, `OAI.UniversalTensorSquare.sg41851`, `OAI.UniversalTensorSquare.sg42368`, `OAI.UniversalTensorSquare.sg43103`, `OAI.UniversalTensorSquare.sg43159`, `OAI.UniversalTensorSquare.sg6197`, `OAI.UniversalTensorSquare.sg6405`, `OAI.UniversalTensorSquare.sg6779`, `OAI.UniversalTensorSquare.sg6937`, `OAI.UniversalTensorSquare.sg7089`, `OAI.UniversalTensorSquare.sg7096`, `OAI.UniversalTensorSquare.sg7171`, `OAI.UniversalTensorSquare.sg7221`, `OAI.UniversalTensorSquare.sg8867`, `OAI.UniversalTensorSquare.sg895`, `OAI.UniversalTensorSquare.sg9286`, `OAI.UniversalTensorSquare.sg9798` and `OAI.UniversalTensorSquare.sg9838` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean (declaration OAI.UniversalTensorSquare.sg589)

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

lemma sg589 : RowSquare [5,1,1,1,1] [2,2,2,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
