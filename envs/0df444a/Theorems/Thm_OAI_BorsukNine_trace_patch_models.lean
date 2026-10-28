-- Prove2me | Theorems.Thm_OAI_BorsukNine_trace_patch_models
-- name    : OAI.BorsukNine.trace_patch_models
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:53:48.181915+00:00
-- url     : https://prove2.me/theorems/dcef1747-9392-44e4-aa69-f3b0c9bfe04a
-- title:
--   OAI.BorsukNine.trace_patch_models: intermediate lemma from OpenAI, A nine-dimensional counterexample to Borsuk's covering assertion (result family 156)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BorsukNine.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A nine-dimensional counterexample to Borsuk's covering assertion (result family 156)*, OpenAI Math Release, September 23, 2026, result family 156, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BorsukNine.trace_patch_models` of [lean/OAI/Geometry/Borsuk/MatrixGeometry/TracePatchModels.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Borsuk/MatrixGeometry/TracePatchModels.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BorsukNine`, with `open Set MeasureTheory`, `open Set SimplicialChains`, `open scoped MatrixOrder Matrix.Norms.L2Operator`):
--
--   ```lean
--   lemma trace_patch_models
--       (hc : Fintype.card (UpperTriangle ν) = Fintype.card ι) (hn : 1 < Fintype.card ι)
--       (F : traceSphere ν → Y) (hF : Continuous F) (hFz : ∀ A, F A ≠ 0)
--       (hFo : ∀ A B : traceSphere ν, B.val = -A.val → F B = -F A)
--       (G : κ → traceSphere ν → Y) (hG : ∀ a, Continuous (G a))
--       (hGz : ∀ a A, G a A ≠ 0)
--       (hGo : ∀ a (A B : traceSphere ν), B.val = -A.val → G a B = -G a A)
--       (K S : κ → Set (traceSphere ν)) (hK : ∀ a, IsClosed (K a)) (hS : ∀ a, IsOpen (S a))
--       (hKS : ∀ a, K a ⊆ S a) (hKd : Pairwise (fun a b => Disjoint (K a) (K b)))
--       {y : Y} (hy : y ≠ 0)
--       (hcover : ∀ A, (∃ d : ℝ, 0 < d ∧ F A = d • y) → ∃ a, A ∈ K a)
--       (hroot : ∀ a A, (∃ d : ℝ, 0 < d ∧ G a A = d • y) → A ∈ K a)
--       (hseg : ∀ a A, A ∈ S a → ∀ t ∈ Icc (0:ℝ) 1, (1-t) • F A + t • G a A ≠ 0)
--       (hhit : ∀ a A, A ∈ S a → ∀ t ∈ Icc (0:ℝ) 1,
--         (∃ d : ℝ, 0 < d ∧ (1-t) • F A + t • G a A = d • y) → A ∈ K a) :
--       (Fintype.card κ : F₂) = 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.BorsukNine.UpperTriangle`, `OAI.BorsukNine.traceSphere` and `OAI.BorsukNine.SimplicialChains.F₂` (definitions bundle `OAIQ058B000` of this split).
--
--   **Used by.** The proof of `OAI.BorsukNine.Admissible.no_free_ridge` of this split imports it.
-- source:
--   OpenAI, A nine-dimensional counterexample to Borsuk's covering assertion (result family 156), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 156; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-nine-dimensional-counterexample-to-Borsuks-covering-assertion-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Borsuk/MatrixGeometry/TracePatchModels.lean (declaration OAI.BorsukNine.trace_patch_models)

import Mathlib
import Definitions.Def_OAIQ058B000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open Set SimplicialChains
open scoped MatrixOrder Matrix.Norms.L2Operator
section TracePatchModels
variable {ν ι κ : Type*} [Fintype ν] [LinearOrder ν] [Nonempty ν] [Fintype ι]
  [Fintype κ] [DecidableEq κ]
local notation "Y" => EuclideanSpace ℝ ι
omit [Nonempty ν] in
lemma trace_patch_models
    (hc : Fintype.card (UpperTriangle ν) = Fintype.card ι) (hn : 1 < Fintype.card ι)
    (F : traceSphere ν → Y) (hF : Continuous F) (hFz : ∀ A, F A ≠ 0)
    (hFo : ∀ A B : traceSphere ν, B.val = -A.val → F B = -F A)
    (G : κ → traceSphere ν → Y) (hG : ∀ a, Continuous (G a))
    (hGz : ∀ a A, G a A ≠ 0)
    (hGo : ∀ a (A B : traceSphere ν), B.val = -A.val → G a B = -G a A)
    (K S : κ → Set (traceSphere ν)) (hK : ∀ a, IsClosed (K a)) (hS : ∀ a, IsOpen (S a))
    (hKS : ∀ a, K a ⊆ S a) (hKd : Pairwise (fun a b => Disjoint (K a) (K b)))
    {y : Y} (hy : y ≠ 0)
    (hcover : ∀ A, (∃ d : ℝ, 0 < d ∧ F A = d • y) → ∃ a, A ∈ K a)
    (hroot : ∀ a A, (∃ d : ℝ, 0 < d ∧ G a A = d • y) → A ∈ K a)
    (hseg : ∀ a A, A ∈ S a → ∀ t ∈ Icc (0:ℝ) 1, (1-t) • F A + t • G a A ≠ 0)
    (hhit : ∀ a A, A ∈ S a → ∀ t ∈ Icc (0:ℝ) 1,
      (∃ d : ℝ, 0 < d ∧ (1-t) • F A + t • G a A = d • y) → A ∈ K a) :
    (Fintype.card κ : F₂) = 1 := by
  sorry
end TracePatchModels
end BorsukNine

end OAI
end
