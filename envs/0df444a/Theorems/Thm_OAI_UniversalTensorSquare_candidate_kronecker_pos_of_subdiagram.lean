-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_candidate_kronecker_pos_of_subdiagram
-- name    : OAI.UniversalTensorSquare.candidate_kronecker_pos_of_subdiagram
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:53:56.147518+00:00
-- url     : https://prove2.me/theorems/c96dcb6d-850e-409a-b4b2-9b9f8722fc35
-- title:
--   OAI.UniversalTensorSquare.candidate_kronecker_pos_of_subdiagram: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.candidate_kronecker_pos_of_subdiagram` of [lean/OAI/RepresentationTheory/UniversalSquare/Support/SubdiagramSupport.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/SubdiagramSupport.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open scoped TensorProduct`, `open Saxl`):
--
--   ```lean
--   theorem candidate_kronecker_pos_of_subdiagram {n M b δ : ℕ} (hM : 4 ≤ M)
--       (a : Tableau n (candidate M b δ)) {ν μ : YoungDiagram}
--       (hνμ : ν ≤ μ) (r : Tableau (candidateBandSize a) ν) (t : Tableau n μ)
--       (f : Representation.IntertwiningMap (spechtRep r)
--         (cyclic (wordRep _ _) (candidateBandWord hM a)).toRepresentation) (hf : f ≠ 0) :
--       0 < kronecker a a t
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.candidate` and `OAI.UniversalTensorSquare.candidateBandSize` (definitions bundle `OAIQ259US007` of this split); `OAI.UniversalTensorSquare.candidateBandWord` (definitions bundle `OAIQ259US021` of this split); `OAI.Saxl.Specht`, `OAI.Saxl.Tableau`, `OAI.Saxl.WordSpace`, `OAI.Saxl.cyclic`, `OAI.Saxl.kronecker`, `OAI.Saxl.spechtRep` and `OAI.Saxl.wordRep` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.band_kronecker_pos` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/SubdiagramSupport.lean (declaration OAI.UniversalTensorSquare.candidate_kronecker_pos_of_subdiagram)

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped TensorProduct
namespace UniversalTensorSquare
open Saxl

theorem candidate_kronecker_pos_of_subdiagram {n M b δ : ℕ} (hM : 4 ≤ M)
    (a : Tableau n (candidate M b δ)) {ν μ : YoungDiagram}
    (hνμ : ν ≤ μ) (r : Tableau (candidateBandSize a) ν) (t : Tableau n μ)
    (f : Representation.IntertwiningMap (spechtRep r)
      (cyclic (wordRep _ _) (candidateBandWord hM a)).toRepresentation) (hf : f ≠ 0) :
    0 < kronecker a a t := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
