-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg3004
-- name    : OAI.UniversalTensorSquare.sg3004
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T09:33:50.856203+00:00
-- url     : https://prove2.me/theorems/5a428241-722a-4aeb-a664-bf601ba91dc2
-- title:
--   OAI.UniversalTensorSquare.sg3004: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg3004` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes6.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes6.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg3004 : RowSquare [8,3,2,1] [3,3,2,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_12All`, `OAI.UniversalTensorSquare.degreeTree62_143All`, `OAI.UniversalTensorSquare.degreeTree62_151All`, `OAI.UniversalTensorSquare.degreeTree62_16All`, `OAI.UniversalTensorSquare.degreeTree62_173All`, `OAI.UniversalTensorSquare.degreeTree62_174All`, `OAI.UniversalTensorSquare.degreeTree62_187All`, `OAI.UniversalTensorSquare.degreeTree62_340All`, `OAI.UniversalTensorSquare.degreeTree62_435All`, `OAI.UniversalTensorSquare.degreeTree62_449All`, `OAI.UniversalTensorSquare.degreeTree62_519All`, `OAI.UniversalTensorSquare.degreeTree62_521All`, `OAI.UniversalTensorSquare.degreeTree62_524All`, `OAI.UniversalTensorSquare.degreeTree62_537All`, `OAI.UniversalTensorSquare.degreeTree62_562All`, `OAI.UniversalTensorSquare.degreeTree62_565All`, `OAI.UniversalTensorSquare.degreeTree62_602All`, `OAI.UniversalTensorSquare.degreeTree62_615All`, `OAI.UniversalTensorSquare.degreeTree62_637All`, `OAI.UniversalTensorSquare.degreeTree62_648All`, `OAI.UniversalTensorSquare.degreeTree62_650All`, `OAI.UniversalTensorSquare.degreeTree62_669All`, `OAI.UniversalTensorSquare.degreeTree62_677All`, `OAI.UniversalTensorSquare.degreeTree62_680All`, `OAI.UniversalTensorSquare.degreeTree62_742All`, `OAI.UniversalTensorSquare.degreeTree62_75All`, `OAI.UniversalTensorSquare.degreeTree62_768All`, `OAI.UniversalTensorSquare.degreeTree62_771All`, `OAI.UniversalTensorSquare.degreeTree62_78All`, `OAI.UniversalTensorSquare.degreeTree62_87All`, `OAI.UniversalTensorSquare.degreeTree62_89All`, `OAI.UniversalTensorSquare.degreeTree62_8All`, `OAI.UniversalTensorSquare.degreeTree62_925All`, `OAI.UniversalTensorSquare.degreeTree62_982All`, `OAI.UniversalTensorSquare.degreeTree62_986All`, `OAI.UniversalTensorSquare.degreeTree62_988All`, `OAI.UniversalTensorSquare.sg21046`, `OAI.UniversalTensorSquare.sg32001`, `OAI.UniversalTensorSquare.sg32211`, `OAI.UniversalTensorSquare.sg32221`, `OAI.UniversalTensorSquare.sg32885`, `OAI.UniversalTensorSquare.sg32945`, `OAI.UniversalTensorSquare.sg33617`, `OAI.UniversalTensorSquare.sg33619`, `OAI.UniversalTensorSquare.sg33672`, `OAI.UniversalTensorSquare.sg33681`, `OAI.UniversalTensorSquare.sg33682`, `OAI.UniversalTensorSquare.sg33685`, `OAI.UniversalTensorSquare.sg33911`, `OAI.UniversalTensorSquare.sg33945`, `OAI.UniversalTensorSquare.sg34064`, `OAI.UniversalTensorSquare.sg34130`, `OAI.UniversalTensorSquare.sg34190`, `OAI.UniversalTensorSquare.sg34192`, `OAI.UniversalTensorSquare.sg34194`, `OAI.UniversalTensorSquare.sg34196`, `OAI.UniversalTensorSquare.sg34235`, `OAI.UniversalTensorSquare.sg34237`, `OAI.UniversalTensorSquare.sg34383`, `OAI.UniversalTensorSquare.sg34385`, `OAI.UniversalTensorSquare.sg34415`, `OAI.UniversalTensorSquare.sg34416`, `OAI.UniversalTensorSquare.sg34417`, `OAI.UniversalTensorSquare.sg34420`, `OAI.UniversalTensorSquare.sg34555`, `OAI.UniversalTensorSquare.sg35837`, `OAI.UniversalTensorSquare.sg35840`, `OAI.UniversalTensorSquare.sg35843`, `OAI.UniversalTensorSquare.sg35845`, `OAI.UniversalTensorSquare.sg35868`, `OAI.UniversalTensorSquare.sg35872`, `OAI.UniversalTensorSquare.sg35874`, `OAI.UniversalTensorSquare.sg35876`, `OAI.UniversalTensorSquare.sg36509`, `OAI.UniversalTensorSquare.sg36597`, `OAI.UniversalTensorSquare.sg37900`, `OAI.UniversalTensorSquare.sg37962`, `OAI.UniversalTensorSquare.sg37969`, `OAI.UniversalTensorSquare.sg38337`, `OAI.UniversalTensorSquare.sg38604`, `OAI.UniversalTensorSquare.sg38607`, `OAI.UniversalTensorSquare.sg39047`, `OAI.UniversalTensorSquare.sg39118`, `OAI.UniversalTensorSquare.sg39161`, `OAI.UniversalTensorSquare.sg39173`, `OAI.UniversalTensorSquare.sg39178`, `OAI.UniversalTensorSquare.sg39280`, `OAI.UniversalTensorSquare.sg39329`, `OAI.UniversalTensorSquare.sg39382`, `OAI.UniversalTensorSquare.sg39623`, `OAI.UniversalTensorSquare.sg39708`, `OAI.UniversalTensorSquare.sg40116`, `OAI.UniversalTensorSquare.sg40117`, `OAI.UniversalTensorSquare.sg40229`, `OAI.UniversalTensorSquare.sg40491`, `OAI.UniversalTensorSquare.sg40498`, `OAI.UniversalTensorSquare.sg40506`, `OAI.UniversalTensorSquare.sg40508`, `OAI.UniversalTensorSquare.sg40510`, `OAI.UniversalTensorSquare.sg40511`, `OAI.UniversalTensorSquare.sg40515`, `OAI.UniversalTensorSquare.sg40807`, `OAI.UniversalTensorSquare.sg40809`, `OAI.UniversalTensorSquare.sg40810`, `OAI.UniversalTensorSquare.sg41530`, `OAI.UniversalTensorSquare.sg41811`, `OAI.UniversalTensorSquare.sg42644`, `OAI.UniversalTensorSquare.sg42776`, `OAI.UniversalTensorSquare.sg42779` and `OAI.UniversalTensorSquare.sg43032` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes6.lean (declaration OAI.UniversalTensorSquare.sg3004)

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

lemma sg3004 : RowSquare [8,3,2,1] [3,3,2,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
