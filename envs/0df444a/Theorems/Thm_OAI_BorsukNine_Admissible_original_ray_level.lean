-- Prove2me | Theorems.Thm_OAI_BorsukNine_Admissible_original_ray_level
-- name    : OAI.BorsukNine.Admissible.original_ray_level
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:44:32.857849+00:00
-- url     : https://prove2.me/theorems/d682c746-e77a-435e-a788-9d34dd9b24f4
-- title:
--   OAI.BorsukNine.Admissible.original_ray_level: intermediate lemma from OpenAI, A nine-dimensional counterexample to Borsuk's covering assertion (result family 156)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BorsukNine.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A nine-dimensional counterexample to Borsuk's covering assertion (result family 156)*, OpenAI Math Release, September 23, 2026, result family 156, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BorsukNine.Admissible.original_ray_level` of [lean/OAI/Geometry/Borsuk/Support/MixedHits.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Borsuk/Support/MixedHits.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BorsukNine`, with `open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator`, `open Set`):
--
--   ```lean
--   lemma Admissible.original_ray_level {f : E → ι → ℝ} (hf : Admissible f) {I : Finset ι}
--       (hI : I.Nonempty) [Nonempty ↥(Iᶜ : Finset ι)]
--       (hmax : ∀ u : E, ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
--       {w : E} (hw : ‖w‖ = 1) (hwi : ∀ i ∈ I, 0 < f w i)
--       {r : ι → ℝ} (hr : ∀ i ∈ I, 0 < r i) (hro : ∀ i ∉ I, r i = 0) (hrs : ∑ i, r i = 1)
--       {z : EuclideanSpace ℝ ↥(Iᶜ : Finset ι)} (hz : ∀ i, 0 < z i) (hzs : ∑ i, z i = 1)
--       {A : M} (hA : A ∈ traceSphere ν) {d : ℝ} (hd : 0 < d)
--       (he : WithLp.toLp 2 (signedExtension f A) = d • blockVector I (1/2:ℝ) r (1/2:ℝ) z) :
--       IsUnit A ∧ HasPositiveLine A ∧ op A⁺ w ≠ 0 ∧ 0 < Matrix.trace A⁻ ∧
--         lineRepresentative w A ∈ orientedLevel f w r
--   ```
--
--   **Definitions.** The statement is written with `OAI.BorsukNine.Admissible`, `OAI.BorsukNine.HasPositiveLine`, `OAI.BorsukNine.blockVector`, `OAI.BorsukNine.lineRepresentative`, `OAI.BorsukNine.orientedLevel`, `OAI.BorsukNine.positiveSupport`, `OAI.BorsukNine.signedExtension` and `OAI.BorsukNine.traceSphere` (definitions bundle `OAIQ058B000` of this split).
--
--   **Used by.** The proofs of `OAI.BorsukNine.Admissible.chart_surgery_impossible` and `OAI.BorsukNine.Admissible.no_free_ridge` of this split import it.
-- source:
--   OpenAI, A nine-dimensional counterexample to Borsuk's covering assertion (result family 156), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 156; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-nine-dimensional-counterexample-to-Borsuks-covering-assertion-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Borsuk/Support/MixedHits.lean (declaration OAI.BorsukNine.Admissible.original_ray_level)

import Mathlib
import Definitions.Def_OAIQ058B000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section MixedHits
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "Y" => EuclideanSpace ℝ ι
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

lemma Admissible.original_ray_level {f : E → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hI : I.Nonempty) [Nonempty ↥(Iᶜ : Finset ι)]
    (hmax : ∀ u : E, ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {w : E} (hw : ‖w‖ = 1) (hwi : ∀ i ∈ I, 0 < f w i)
    {r : ι → ℝ} (hr : ∀ i ∈ I, 0 < r i) (hro : ∀ i ∉ I, r i = 0) (hrs : ∑ i, r i = 1)
    {z : EuclideanSpace ℝ ↥(Iᶜ : Finset ι)} (hz : ∀ i, 0 < z i) (hzs : ∑ i, z i = 1)
    {A : M} (hA : A ∈ traceSphere ν) {d : ℝ} (hd : 0 < d)
    (he : WithLp.toLp 2 (signedExtension f A) = d • blockVector I (1/2:ℝ) r (1/2:ℝ) z) :
    IsUnit A ∧ HasPositiveLine A ∧ op A⁺ w ≠ 0 ∧ 0 < Matrix.trace A⁻ ∧
      lineRepresentative w A ∈ orientedLevel f w r := by
  sorry

end MixedHits
end BorsukNine

end OAI
end
