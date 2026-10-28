-- Prove2me | Theorems.Thm_OAI_MaxCutGames_Decoder_MatrixGapChoice_exists_inverse_parameters
-- name    : OAI.MaxCutGames.Decoder.MatrixGapChoice.exists_inverse_parameters
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T17:53:26.655506+00:00
-- url     : https://prove2.me/theorems/3ffa4d4c-ffc6-4c0b-b77b-af32cef19d85
-- title:
--   OAI.MaxCutGames.Decoder.MatrixGapChoice.exists_inverse_parameters: intermediate lemma from OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaxCutGames.Decoder.MatrixGapChoice.exists_inverse_parameters` of [lean/OAI/Computability/MaxCut/Encoding/ActualGoodRows.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Encoding/ActualGoodRows.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaxCutGames.Decoder.MatrixGapChoice`, with `open Integration.BinaryLinear Reduction ActualSource`, `open Inverse.Shortcode (Mat HasAffineSlice InversePrinciple equalityAcceptance)`):
--
--   ```lean
--   theorem exists_inverse_parameters (hinverse : InversePrinciple) (rstar : ℕ) :
--       Nonempty (InverseParameters rstar)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaxCutGames.Inverse.Shortcode.InversePrinciple` (definitions bundle `OAIQ087A012` of this split); `OAI.MaxCutGames.Decoder.MatrixGapChoice.InverseParameters` (definitions bundle `OAIQ087A021` of this split).
--
--   **Used by.** The proof of `OAI.MaxCutGames.theorem11` of this split imports it.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Encoding/ActualGoodRows.lean (declaration OAI.MaxCutGames.Decoder.MatrixGapChoice.exists_inverse_parameters)

import Mathlib
import Definitions.Def_OAIQ087A012
import Definitions.Def_OAIQ087A021

section

attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Decoder.MatrixGapChoice

open Integration.BinaryLinear Reduction ActualSource
open Inverse.Shortcode (Mat HasAffineSlice InversePrinciple equalityAcceptance)

noncomputable section

theorem exists_inverse_parameters (hinverse : InversePrinciple) (rstar : ℕ) :
    Nonempty (InverseParameters rstar) := by
  sorry

end
end MaxCutGames.Decoder.MatrixGapChoice

end OAI
end
