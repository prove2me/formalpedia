-- Prove2me | Theorems.Thm_OAI_BorsukNine_Admissible_regular_facet_level_even
-- name    : OAI.BorsukNine.Admissible.regular_facet_level_even
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:43:14.001391+00:00
-- url     : https://prove2.me/theorems/e628a054-cd79-480a-823e-42b3ac90a5da
-- title:
--   OAI.BorsukNine.Admissible.regular_facet_level_even: intermediate lemma from OpenAI, A nine-dimensional counterexample to Borsuk's covering assertion (result family 156)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BorsukNine.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A nine-dimensional counterexample to Borsuk's covering assertion (result family 156)*, OpenAI Math Release, September 23, 2026, result family 156, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BorsukNine.Admissible.regular_facet_level_even` of [lean/OAI/Geometry/Borsuk/LocalParity/SphereParity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Borsuk/LocalParity/SphereParity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BorsukNine`, with `open Set MeasureTheory`, `open Set SimplicialChains`, `open scoped RealInnerProductSpace`):
--
--   ```lean
--   lemma Admissible.regular_facet_level_even {f : E → ι → ℝ} (hf : Admissible f)
--       (hk : 0 < k) {I : Finset ι} (a : Fin (k+1) ≃ ↥I)
--       (hfree : ∀ u : E, ‖u‖ = 1 → (∀ j : Fin k, 0 < f u (a j.succ).val) → positiveSupport f u ⊆ I)
--       {w : E} (hw : ‖w‖ = 1) (hwi : ∀ i ∈ I, 0 < f w i)
--       (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪w,e v⟫ = 0)
--       (hes : ∀ u, ⟪w,u⟫ = 0 → ∃ v, e v = u) {z : W} (hz : z ∈ simplexInterior k)
--       (hr : ∀ v, baseCoordinates f w e a v = z → (fderiv ℝ (baseCoordinates f w e a) v).det ≠ 0)
--       (hfin : (orientedLevel f w (facetPoint a z)).Finite) :
--       (Nat.card (orientedLevel f w (facetPoint a z)) : F₂) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.BorsukNine.Admissible`, `OAI.BorsukNine.baseCoordinates`, `OAI.BorsukNine.facetPoint`, `OAI.BorsukNine.orientedLevel`, `OAI.BorsukNine.positiveSupport`, `OAI.BorsukNine.simplexInterior` and `OAI.BorsukNine.SimplicialChains.F₂` (definitions bundle `OAIQ058B000` of this split).
--
--   **Used by.** The proof of `OAI.BorsukNine.Admissible.no_free_ridge` of this split imports it.
-- source:
--   OpenAI, A nine-dimensional counterexample to Borsuk's covering assertion (result family 156), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 156; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-nine-dimensional-counterexample-to-Borsuks-covering-assertion-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Borsuk/LocalParity/SphereParity.lean (declaration OAI.BorsukNine.Admissible.regular_facet_level_even)

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
open scoped RealInnerProductSpace
section SphereParity
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ (Fin (k+1))
local notation "W" => EuclideanSpace ℝ (Fin k)

lemma Admissible.regular_facet_level_even {f : E → ι → ℝ} (hf : Admissible f)
    (hk : 0 < k) {I : Finset ι} (a : Fin (k+1) ≃ ↥I)
    (hfree : ∀ u : E, ‖u‖ = 1 → (∀ j : Fin k, 0 < f u (a j.succ).val) → positiveSupport f u ⊆ I)
    {w : E} (hw : ‖w‖ = 1) (hwi : ∀ i ∈ I, 0 < f w i)
    (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪w,e v⟫ = 0)
    (hes : ∀ u, ⟪w,u⟫ = 0 → ∃ v, e v = u) {z : W} (hz : z ∈ simplexInterior k)
    (hr : ∀ v, baseCoordinates f w e a v = z → (fderiv ℝ (baseCoordinates f w e a) v).det ≠ 0)
    (hfin : (orientedLevel f w (facetPoint a z)).Finite) :
    (Nat.card (orientedLevel f w (facetPoint a z)) : F₂) = 0 := by
  sorry
end SphereParity
end BorsukNine

end OAI
end
