-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_semantic_capacity_dichotomy
-- name    : OAI.UniversalTensorSquare.semantic_capacity_dichotomy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T13:38:16.614792+00:00
-- url     : https://prove2.me/theorems/7fe1ef0a-c8ac-468c-8827-214223eeb08a
-- title:
--   OAI.UniversalTensorSquare.semantic_capacity_dichotomy: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.semantic_capacity_dichotomy` of [lean/OAI/RepresentationTheory/UniversalSquare/Capacity/RegionExhaustion.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Capacity/RegionExhaustion.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Balance Saxl.Columns`):
--
--   ```lean
--   theorem semantic_capacity_dichotomy (μ θ : YoungDiagram) {n M r : ℕ}
--       (hn : 0 < n) (hM : 1 ≤ M) (hr : 0 < r) (hc : μ.card = n) (ht : θ.card = n)
--       (P : List ℕ → Prop)
--       (check : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
--         ∀ a ∈ List.range θ.rowLens.length, ∀ b ∈ List.range θ.rowLens.length,
--           semanticResidualCheck n M r (d+1) (e+1) (a+1) (b+1) θ.rowLens P) :
--       BandTest M r μ ∨ BandTest M r μ.transpose ∨ Dominates μ θ ∨
--         Dominates μ.transpose θ ∨ P μ.rowLens
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Dominates` and `OAI.UniversalTensorSquare.BandTest` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.semanticResidualCheck` (definitions bundle `OAIQ259US012` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degree_pos14` and `OAI.UniversalTensorSquare.degree_pos22` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Capacity/RegionExhaustion.lean (declaration OAI.UniversalTensorSquare.semantic_capacity_dichotomy)

import Mathlib
import Definitions.Def_OAIQ259US012

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

theorem semantic_capacity_dichotomy (μ θ : YoungDiagram) {n M r : ℕ}
    (hn : 0 < n) (hM : 1 ≤ M) (hr : 0 < r) (hc : μ.card = n) (ht : θ.card = n)
    (P : List ℕ → Prop)
    (check : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
      ∀ a ∈ List.range θ.rowLens.length, ∀ b ∈ List.range θ.rowLens.length,
        semanticResidualCheck n M r (d+1) (e+1) (a+1) (b+1) θ.rowLens P) :
    BandTest M r μ ∨ BandTest M r μ.transpose ∨ Dominates μ θ ∨
      Dominates μ.transpose θ ∨ P μ.rowLens := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
