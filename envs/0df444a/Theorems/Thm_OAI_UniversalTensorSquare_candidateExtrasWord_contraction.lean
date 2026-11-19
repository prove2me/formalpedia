-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_candidateExtrasWord_contraction
-- name    : OAI.UniversalTensorSquare.candidateExtrasWord_contraction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:51:47.04393+00:00
-- url     : https://prove2.me/theorems/de73b4e9-8a0d-492e-b253-9f090df3c0a2
-- title:
--   OAI.UniversalTensorSquare.candidateExtrasWord_contraction: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.candidateExtrasWord_contraction` of [lean/OAI/RepresentationTheory/UniversalSquare/Contraction/BandContractions.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Contraction/BandContractions.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl`, `open Saxl.FlagColumns`):
--
--   ```lean
--   theorem candidateExtrasWord_contraction {M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
--       (hr : r = 2*b+δ) (s₁ s₂ : Tableau r (ShortColumns.shape b δ))
--       (η : YoungDiagram) (hη : η.card = 2*r)
--       (he : ∀ i, Even (η.colLen i)) (hd : η.rowLen 0 ≤ 8)
--       (rs : List ℕ) (hn : rs.sum = 2*r) (e : Columns.Cells rs ≃ η.cells)
--       (er : ∀ c, (e c).val.1 = Columns.row c)
--       (ec : ∀ c c', (e c).val.2 = (e c').val.2 ↔ Columns.col c = Columns.col c') :
--       ∃ (g : Equiv.Perm (Fin rs.sum))
--         (Q : ℕ → Fin ((candidate M b δ).transpose.colLen 0 * (candidate M b δ).colLen 0) → ℂ),
--         (∀ i a, candidatePathAlphabet M b δ a → Q i a = 0) ∧
--         dotProduct (blocks rs Q) (relabelWord g
--           (relabelWord (finCongr hn).symm (candidateExtrasWord hM s₁ s₂))) ≠ 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.relabelWord`, `OAI.Saxl.Columns.Cells`, `OAI.Saxl.Columns.col` and `OAI.Saxl.Columns.row` (definitions bundle `OAIQ259US000` of this split); `OAI.Saxl.ShortColumns.shape` (definitions bundle `OAIQ259US001` of this split); `OAI.Saxl.FlagColumns.blocks` (definitions bundle `OAIQ259US006` of this split); `OAI.UniversalTensorSquare.candidate` and `OAI.UniversalTensorSquare.candidatePathAlphabet` (definitions bundle `OAIQ259US007` of this split); `OAI.UniversalTensorSquare.candidateExtrasWord` (definitions bundle `OAIQ259US021` of this split); `OAI.Saxl.Tableau` and `OAI.Saxl.WordSpace` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.band_kronecker_pos` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Contraction/BandContractions.lean (declaration OAI.UniversalTensorSquare.candidateExtrasWord_contraction)

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

theorem candidateExtrasWord_contraction {M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (hr : r = 2*b+δ) (s₁ s₂ : Tableau r (ShortColumns.shape b δ))
    (η : YoungDiagram) (hη : η.card = 2*r)
    (he : ∀ i, Even (η.colLen i)) (hd : η.rowLen 0 ≤ 8)
    (rs : List ℕ) (hn : rs.sum = 2*r) (e : Columns.Cells rs ≃ η.cells)
    (er : ∀ c, (e c).val.1 = Columns.row c)
    (ec : ∀ c c', (e c).val.2 = (e c').val.2 ↔ Columns.col c = Columns.col c') :
    ∃ (g : Equiv.Perm (Fin rs.sum))
      (Q : ℕ → Fin ((candidate M b δ).transpose.colLen 0 * (candidate M b δ).colLen 0) → ℂ),
      (∀ i a, candidatePathAlphabet M b δ a → Q i a = 0) ∧
      dotProduct (blocks rs Q) (relabelWord g
        (relabelWord (finCongr hn).symm (candidateExtrasWord hM s₁ s₂))) ≠ 0 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
