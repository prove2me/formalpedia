-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_candidate_refined_pos
-- name    : OAI.UniversalTensorSquare.candidate_refined_pos
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T17:10:13.812324+00:00
-- url     : https://prove2.me/theorems/8af10d6d-7dd7-409e-8bed-b5b891bff234
-- title:
--   OAI.UniversalTensorSquare.candidate_refined_pos: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.candidate_refined_pos` of [lean/OAI/RepresentationTheory/UniversalSquare/Balance/ExceptionalPacking.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Balance/ExceptionalPacking.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Balance Saxl.Columns`):
--
--   ```lean
--   theorem candidate_refined_pos {n M b δ r : ℕ} (hM : 9 ≤ M) (hb : b ≤ M-2)
--       (hδ : δ ≤ 1) (hr : r = 2*b+δ) (hrpos : 0 < r)
--       (hn : (candidate M b δ).card = n)
--       (q : List ℕ) (hq : q.SortedGE) (hqp : ∀ a ∈ q, 0 < a) (hqn : q.sum = n)
--       (p : PackingPlan) (hv : p.Valid (M+b+δ)) (hbands : BandsValid p.bands)
--       (hcols : p.columns.Perm ([M+b+δ,M-1+b] ++
--         (List.range' 3 (M-4)).reverse ++ List.replicate (b+1) 2 ++ List.replicate (1+δ) 1))
--       (hparts : p.parts.Perm q)
--       (check : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
--         ∀ a ∈ List.range q.length, ∀ c ∈ List.range q.length,
--           refinedCheck n M r (d+1) (e+1) (a+1) (c+1) q)
--       (μ : YoungDiagram) (hμ : μ.card = n) :
--       0 < kronecker (canonicalTableau (candidate M b δ) hn)
--         (canonicalTableau (candidate M b δ) hn) (canonicalTableau μ hμ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Balance.BandsValid` (definitions bundle `OAIQ259US000` of this split); `OAI.Saxl.Balance.PackingPlan`, `OAI.Saxl.Balance.PackingPlan.Valid`, `OAI.Saxl.Balance.PackingPlan.bands`, `OAI.Saxl.Balance.PackingPlan.columns` and `OAI.Saxl.Balance.PackingPlan.parts` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.candidate` (definitions bundle `OAIQ259US007` of this split); `OAI.UniversalTensorSquare.refinedCheck` (definitions bundle `OAIQ259US012` of this split); `OAI.Saxl.canonicalTableau` and `OAI.Saxl.kronecker` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.exceptional_pos106`, `OAI.UniversalTensorSquare.exceptional_pos108`, `OAI.UniversalTensorSquare.exceptional_pos110`, `OAI.UniversalTensorSquare.exceptional_pos114`, `OAI.UniversalTensorSquare.exceptional_pos149`, `OAI.UniversalTensorSquare.exceptional_pos71`, `OAI.UniversalTensorSquare.exceptional_pos73`, `OAI.UniversalTensorSquare.exceptional_pos75`, `OAI.UniversalTensorSquare.exceptional_pos77`, `OAI.UniversalTensorSquare.exceptional_pos79`, `OAI.UniversalTensorSquare.exceptional_pos81`, `OAI.UniversalTensorSquare.exceptional_pos83`, `OAI.UniversalTensorSquare.exceptional_pos85` and `OAI.UniversalTensorSquare.exceptional_pos87` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Balance/ExceptionalPacking.lean (declaration OAI.UniversalTensorSquare.candidate_refined_pos)

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US007
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

theorem candidate_refined_pos {n M b δ r : ℕ} (hM : 9 ≤ M) (hb : b ≤ M-2)
    (hδ : δ ≤ 1) (hr : r = 2*b+δ) (hrpos : 0 < r)
    (hn : (candidate M b δ).card = n)
    (q : List ℕ) (hq : q.SortedGE) (hqp : ∀ a ∈ q, 0 < a) (hqn : q.sum = n)
    (p : PackingPlan) (hv : p.Valid (M+b+δ)) (hbands : BandsValid p.bands)
    (hcols : p.columns.Perm ([M+b+δ,M-1+b] ++
      (List.range' 3 (M-4)).reverse ++ List.replicate (b+1) 2 ++ List.replicate (1+δ) 1))
    (hparts : p.parts.Perm q)
    (check : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
      ∀ a ∈ List.range q.length, ∀ c ∈ List.range q.length,
        refinedCheck n M r (d+1) (e+1) (a+1) (c+1) q)
    (μ : YoungDiagram) (hμ : μ.card = n) :
    0 < kronecker (canonicalTableau (candidate M b δ) hn)
      (canonicalTableau (candidate M b δ) hn) (canonicalTableau μ hμ) := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
