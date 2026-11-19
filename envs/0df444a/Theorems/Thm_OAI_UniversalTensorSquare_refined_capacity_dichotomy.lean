-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_refined_capacity_dichotomy
-- name    : OAI.UniversalTensorSquare.refined_capacity_dichotomy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T17:19:09.215283+00:00
-- url     : https://prove2.me/theorems/320f1acd-590c-4c2c-a157-d7a73de51506
-- title:
--   OAI.UniversalTensorSquare.refined_capacity_dichotomy: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.refined_capacity_dichotomy` of [lean/OAI/RepresentationTheory/UniversalSquare/Capacity/RefinedExhaustion.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Capacity/RefinedExhaustion.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl`):
--
--   ```lean
--   theorem refined_capacity_dichotomy (μ θ : YoungDiagram) {n M r : ℕ}
--       (hn : 0 < n) (hM : 9 ≤ M) (hr : 0 < r) (hc : μ.card = n) (ht : θ.card = n)
--       (check : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
--         ∀ a ∈ List.range θ.rowLens.length, ∀ b ∈ List.range θ.rowLens.length,
--           refinedCheck n M r (d+1) (e+1) (a+1) (b+1) θ.rowLens) :
--       colPrefix μ 4 ≤ 2*M-2 ∨ colPrefix μ.transpose 4 ≤ 2*M-2 ∨
--         BandTest M r μ ∨ BandTest M r μ.transpose ∨ Dominates μ θ ∨ Dominates μ.transpose θ
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Dominates`, `OAI.UniversalTensorSquare.BandTest` and `OAI.UniversalTensorSquare.colPrefix` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.refinedCheck` (definitions bundle `OAIQ259US012` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.candidate_refined_pos` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Capacity/RefinedExhaustion.lean (declaration OAI.UniversalTensorSquare.refined_capacity_dichotomy)

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
open Saxl

theorem refined_capacity_dichotomy (μ θ : YoungDiagram) {n M r : ℕ}
    (hn : 0 < n) (hM : 9 ≤ M) (hr : 0 < r) (hc : μ.card = n) (ht : θ.card = n)
    (check : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
      ∀ a ∈ List.range θ.rowLens.length, ∀ b ∈ List.range θ.rowLens.length,
        refinedCheck n M r (d+1) (e+1) (a+1) (b+1) θ.rowLens) :
    colPrefix μ 4 ≤ 2*M-2 ∨ colPrefix μ.transpose 4 ≤ 2*M-2 ∨
      BandTest M r μ ∨ BandTest M r μ.transpose ∨ Dominates μ θ ∨ Dominates μ.transpose θ := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
