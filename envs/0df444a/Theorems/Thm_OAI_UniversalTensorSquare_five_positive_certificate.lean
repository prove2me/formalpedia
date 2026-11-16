-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_five_positive_certificate
-- name    : OAI.UniversalTensorSquare.five_positive_certificate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-15T21:51:40.69654+00:00
-- url     : https://prove2.me/theorems/5195cbce-7544-45f4-b3cd-163fa0d944af
-- title:
--   OAI.UniversalTensorSquare.five_positive_certificate: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.five_positive_certificate` of [lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeFive.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeFive.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns`):
--
--   ```lean
--   lemma five_positive_certificate (rs : List ℕ) (hs : rs.SortedGE)
--       (hp : ∀ a ∈ rs, 0 < a) (hn : rs.sum = 5)
--       (eb : Equiv.Perm (Fin 5)) (et : Fin 5 ≃ Fin rs.sum)
--       (L : ℕ → ℕ → ℕ → ℤ)
--       (hc : contractionInteger [3,1,1] [3,1,1] rs (Equiv.refl _) eb et L ≠ 0) :
--       0 < kronecker (canonicalTableau fiveWitness fiveWitness_card)
--         (canonicalTableau fiveWitness fiveWitness_card)
--         (canonicalTableau (diagramOfCols rs hs) ((diagramOfCols_card rs hs hp).trans hn))
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.diagramOfCols` and `OAI.UniversalTensorSquare.fiveWitness` (definitions bundle `OAIQ259US002` of this split); `OAI.Saxl.Columns.contractionInteger` (definitions bundle `OAIQ259US006` of this split); `OAI.UniversalTensorSquare.diagramOfCols_card` and `OAI.UniversalTensorSquare.fiveWitness_card` (definitions bundle `OAIQ259US012` of this split); `OAI.Saxl.canonicalTableau` and `OAI.Saxl.kronecker` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.five_positive311`, `OAI.UniversalTensorSquare.five_positive32`, `OAI.UniversalTensorSquare.five_positive41` and `OAI.UniversalTensorSquare.five_positive5` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeFive.lean (declaration OAI.UniversalTensorSquare.five_positive_certificate)

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US012

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Saxl Saxl.Columns
namespace UniversalTensorSquare

noncomputable section

lemma five_positive_certificate (rs : List ℕ) (hs : rs.SortedGE)
    (hp : ∀ a ∈ rs, 0 < a) (hn : rs.sum = 5)
    (eb : Equiv.Perm (Fin 5)) (et : Fin 5 ≃ Fin rs.sum)
    (L : ℕ → ℕ → ℕ → ℤ)
    (hc : contractionInteger [3,1,1] [3,1,1] rs (Equiv.refl _) eb et L ≠ 0) :
    0 < kronecker (canonicalTableau fiveWitness fiveWitness_card)
      (canonicalTableau fiveWitness fiveWitness_card)
      (canonicalTableau (diagramOfCols rs hs) ((diagramOfCols_card rs hs hp).trans hn)) := by
  sorry

universe u

end
end UniversalTensorSquare
end

end OAI
end
