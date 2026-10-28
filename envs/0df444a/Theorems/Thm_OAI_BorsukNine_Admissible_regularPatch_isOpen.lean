-- Prove2me | Theorems.Thm_OAI_BorsukNine_Admissible_regularPatch_isOpen
-- name    : OAI.BorsukNine.Admissible.regularPatch_isOpen
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:44:09.673975+00:00
-- url     : https://prove2.me/theorems/bd514c67-ab99-453f-90d3-ed1920311425
-- title:
--   OAI.BorsukNine.Admissible.regularPatch_isOpen: intermediate lemma from OpenAI, A nine-dimensional counterexample to Borsuk's covering assertion (result family 156)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BorsukNine.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A nine-dimensional counterexample to Borsuk's covering assertion (result family 156)*, OpenAI Math Release, September 23, 2026, result family 156, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BorsukNine.Admissible.regularPatch_isOpen` of [lean/OAI/Geometry/Borsuk/LocalParity/RegularPatch.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Borsuk/LocalParity/RegularPatch.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BorsukNine`, with `open Set MeasureTheory`, `open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator`, `open Set`):
--
--   ```lean
--   lemma Admissible.regularPatch_isOpen {f : E → ι → ℝ} (hf : Admissible f)
--       (I : Finset ι) (w c : E) (e : W →ₗᵢ[ℝ] E) (δ : ℝ) : IsOpen (regularPatch f I w c e δ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.BorsukNine.Admissible`, `OAI.BorsukNine.regularPatch` and `OAI.BorsukNine.traceSphere` (definitions bundle `OAIQ058B000` of this split).
--
--   **Used by.** The proof of `OAI.BorsukNine.Admissible.no_free_ridge` of this split imports it.
-- source:
--   OpenAI, A nine-dimensional counterexample to Borsuk's covering assertion (result family 156), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 156; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-nine-dimensional-counterexample-to-Borsuks-covering-assertion-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Borsuk/LocalParity/RegularPatch.lean (declaration OAI.BorsukNine.Admissible.regularPatch_isOpen)

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
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set

section RegularPatch
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ (Fin (k+1))
local notation "W" => EuclideanSpace ℝ (Fin k)

omit [DecidableEq ι] in
lemma Admissible.regularPatch_isOpen {f : E → ι → ℝ} (hf : Admissible f)
    (I : Finset ι) (w c : E) (e : W →ₗᵢ[ℝ] E) (δ : ℝ) : IsOpen (regularPatch f I w c e δ) := by
  sorry
end RegularPatch
end BorsukNine

end OAI
end
