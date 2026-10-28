-- Prove2me | Theorems.Thm_OAI_BorsukNine_Admissible_mixedHomotopy_hit
-- name    : OAI.BorsukNine.Admissible.mixedHomotopy_hit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:42:41.956847+00:00
-- url     : https://prove2.me/theorems/16921bc9-0513-4db8-ac56-1fb3f1e97878
-- title:
--   OAI.BorsukNine.Admissible.mixedHomotopy_hit: intermediate lemma from OpenAI, A nine-dimensional counterexample to Borsuk's covering assertion (result family 156)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BorsukNine.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A nine-dimensional counterexample to Borsuk's covering assertion (result family 156)*, OpenAI Math Release, September 23, 2026, result family 156, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BorsukNine.Admissible.mixedHomotopy_hit` of [lean/OAI/Geometry/Borsuk/Support/MixedHits.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Borsuk/Support/MixedHits.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BorsukNine`, with `open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator`, `open Set`):
--
--   ```lean
--   lemma Admissible.mixedHomotopy_hit {f : E → ι → ℝ} (hf : Admissible f) {I : Finset ι}
--       (hI : I.Nonempty)
--       (hmax : ∀ u : E, ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
--       {w c : E} (hc : c ∈ commonPositiveCone f I) (hcn : ‖c‖ = 1)
--       (g : M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) (hg : ∀ Q ∈ matrixFibre c, ∑ i, g Q i = 1)
--       {r : ι → ℝ} (hro : ∀ i ∉ I, r i = 0) (hrs : ∑ i, r i = 1)
--       {z : EuclideanSpace ℝ ↥(Iᶜ : Finset ι)} (hzs : ∑ i, z i = 1)
--       {t d : ℝ} (ht : t ∈ Icc 0 1) (hd : 0 < d) {A : M}
--       (hSA : A ∈ traceSphere ν) (hA : A ∈ purityChart f I w c)
--       (he : mixedHomotopy f I w c g t A = d • blockVector I (1/2:ℝ) r (1/2:ℝ) z) :
--       lineRepresentative w A ∈ orientedLevel f w r ∧
--         fibreHomotopy f I c g t (lineRepresentative w A) (negativeFibre A) = z ∧
--         A = (1/2:ℝ) • rankOne (lineRepresentative w A) - (1/2:ℝ) • negativeFibre A
--   ```
--
--   **Definitions.** The statement is written with `OAI.BorsukNine.Admissible`, `OAI.BorsukNine.blockVector`, `OAI.BorsukNine.commonPositiveCone`, `OAI.BorsukNine.fibreHomotopy`, `OAI.BorsukNine.lineRepresentative`, `OAI.BorsukNine.matrixFibre`, `OAI.BorsukNine.mixedHomotopy`, `OAI.BorsukNine.negativeFibre`, `OAI.BorsukNine.orientedLevel`, `OAI.BorsukNine.positiveSupport`, `OAI.BorsukNine.purityChart`, `OAI.BorsukNine.rankOne` and `OAI.BorsukNine.traceSphere` (definitions bundle `OAIQ058B000` of this split).
--
--   **Used by.** The proof of `OAI.BorsukNine.Admissible.chart_surgery_impossible` of this split imports it.
-- source:
--   OpenAI, A nine-dimensional counterexample to Borsuk's covering assertion (result family 156), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 156; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-nine-dimensional-counterexample-to-Borsuks-covering-assertion-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Borsuk/Support/MixedHits.lean (declaration OAI.BorsukNine.Admissible.mixedHomotopy_hit)

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

lemma Admissible.mixedHomotopy_hit {f : E → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hI : I.Nonempty)
    (hmax : ∀ u : E, ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {w c : E} (hc : c ∈ commonPositiveCone f I) (hcn : ‖c‖ = 1)
    (g : M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) (hg : ∀ Q ∈ matrixFibre c, ∑ i, g Q i = 1)
    {r : ι → ℝ} (hro : ∀ i ∉ I, r i = 0) (hrs : ∑ i, r i = 1)
    {z : EuclideanSpace ℝ ↥(Iᶜ : Finset ι)} (hzs : ∑ i, z i = 1)
    {t d : ℝ} (ht : t ∈ Icc 0 1) (hd : 0 < d) {A : M}
    (hSA : A ∈ traceSphere ν) (hA : A ∈ purityChart f I w c)
    (he : mixedHomotopy f I w c g t A = d • blockVector I (1/2:ℝ) r (1/2:ℝ) z) :
    lineRepresentative w A ∈ orientedLevel f w r ∧
      fibreHomotopy f I c g t (lineRepresentative w A) (negativeFibre A) = z ∧
      A = (1/2:ℝ) • rankOne (lineRepresentative w A) - (1/2:ℝ) • negativeFibre A := by
  sorry

end MixedHits
end BorsukNine

end OAI
end
