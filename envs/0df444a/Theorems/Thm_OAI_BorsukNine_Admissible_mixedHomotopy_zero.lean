-- Prove2me | Theorems.Thm_OAI_BorsukNine_Admissible_mixedHomotopy_zero
-- name    : OAI.BorsukNine.Admissible.mixedHomotopy_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:42:51.317901+00:00
-- url     : https://prove2.me/theorems/e697a184-d154-45a2-9f00-247eba710e86
-- title:
--   OAI.BorsukNine.Admissible.mixedHomotopy_zero: intermediate lemma from OpenAI, A nine-dimensional counterexample to Borsuk's covering assertion (result family 156)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BorsukNine.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A nine-dimensional counterexample to Borsuk's covering assertion (result family 156)*, OpenAI Math Release, September 23, 2026, result family 156, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BorsukNine.Admissible.mixedHomotopy_zero` of [lean/OAI/Geometry/Borsuk/Support/MixedHomotopy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Borsuk/Support/MixedHomotopy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BorsukNine`, with `open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator`, `open Set`):
--
--   ```lean
--   lemma Admissible.mixedHomotopy_zero {f : E → ι → ℝ} (hf : Admissible f) {I : Finset ι}
--       (hmax : ∀ u : E, ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
--       {w c : E} (g : M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) {A : M}
--       (hSA : IsSelfAdjoint A) (hA : A ∈ purityChart f I w c) :
--       mixedHomotopy f I w c g 0 A = WithLp.toLp 2 (signedExtension f A)
--   ```
--
--   **Definitions.** The statement is written with `OAI.BorsukNine.Admissible`, `OAI.BorsukNine.mixedHomotopy`, `OAI.BorsukNine.positiveSupport`, `OAI.BorsukNine.purityChart` and `OAI.BorsukNine.signedExtension` (definitions bundle `OAIQ058B000` of this split).
--
--   **Used by.** The proofs of `OAI.BorsukNine.Admissible.chart_surgery_impossible` and `OAI.BorsukNine.Admissible.original_ray_level` of this split import it.
-- source:
--   OpenAI, A nine-dimensional counterexample to Borsuk's covering assertion (result family 156), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 156; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-nine-dimensional-counterexample-to-Borsuks-covering-assertion-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Borsuk/Support/MixedHomotopy.lean (declaration OAI.BorsukNine.Admissible.mixedHomotopy_zero)

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
section MixedHomotopy
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ

lemma Admissible.mixedHomotopy_zero {f : E → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hmax : ∀ u : E, ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {w c : E} (g : M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) {A : M}
    (hSA : IsSelfAdjoint A) (hA : A ∈ purityChart f I w c) :
    mixedHomotopy f I w c g 0 A = WithLp.toLp 2 (signedExtension f A) := by
  sorry

end MixedHomotopy
end BorsukNine

end OAI
end
