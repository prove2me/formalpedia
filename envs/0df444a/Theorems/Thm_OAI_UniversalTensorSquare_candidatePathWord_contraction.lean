-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_candidatePathWord_contraction
-- name    : OAI.UniversalTensorSquare.candidatePathWord_contraction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:53:48.082045+00:00
-- url     : https://prove2.me/theorems/b3ff5c48-10ef-444b-8ff8-f07585165199
-- title:
--   OAI.UniversalTensorSquare.candidatePathWord_contraction: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.candidatePathWord_contraction` of [lean/OAI/RepresentationTheory/UniversalSquare/Contraction/BandContractions.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Contraction/BandContractions.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl`, `open Saxl.FlagColumns`):
--
--   ```lean
--   theorem candidatePathWord_contraction {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
--       (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ))
--       (rs : List ℕ) (hrs : ∀ a ∈ rs, 1 ≤ a ∧ a ≤ 4) (hn : rs.sum = 2*M-1) :
--       ∃ N : ℕ → Fin ((candidate M b δ).transpose.colLen 0 * (candidate M b δ).colLen 0) → ℂ,
--         (∀ i a, ¬candidatePathAlphabet M b δ a → N i a = 0) ∧
--         dotProduct (blocks rs N)
--           (relabelWord (finCongr hn).symm (candidatePathWord hM t s₁ s₂)) ≠ 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.relabelWord` (definitions bundle `OAIQ259US000` of this split); `OAI.Saxl.ShortColumns.shape` (definitions bundle `OAIQ259US001` of this split); `OAI.Saxl.FlagColumns.blocks` (definitions bundle `OAIQ259US006` of this split); `OAI.UniversalTensorSquare.candidate` and `OAI.UniversalTensorSquare.candidatePathAlphabet` (definitions bundle `OAIQ259US007` of this split); `OAI.UniversalTensorSquare.candidatePathWord` (definitions bundle `OAIQ259US021` of this split); `OAI.Saxl.Tableau` and `OAI.Saxl.WordSpace` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.band_kronecker_pos` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Contraction/BandContractions.lean (declaration OAI.UniversalTensorSquare.candidatePathWord_contraction)

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
namespace UniversalTensorSquare
open Saxl
open Saxl.FlagColumns

theorem candidatePathWord_contraction {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ))
    (rs : List ℕ) (hrs : ∀ a ∈ rs, 1 ≤ a ∧ a ≤ 4) (hn : rs.sum = 2*M-1) :
    ∃ N : ℕ → Fin ((candidate M b δ).transpose.colLen 0 * (candidate M b δ).colLen 0) → ℂ,
      (∀ i a, ¬candidatePathAlphabet M b δ a → N i a = 0) ∧
      dotProduct (blocks rs N)
        (relabelWord (finCongr hn).symm (candidatePathWord hM t s₁ s₂)) ≠ 0 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
