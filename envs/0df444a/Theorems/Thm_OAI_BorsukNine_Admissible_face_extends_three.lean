-- Prove2me | Theorems.Thm_OAI_BorsukNine_Admissible_face_extends_three
-- name    : OAI.BorsukNine.Admissible.face_extends_three
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:40:53.381298+00:00
-- url     : https://prove2.me/theorems/aaf6b2bc-f563-4ee2-b0eb-9ddffc332afd
-- title:
--   OAI.BorsukNine.Admissible.face_extends_three: intermediate lemma from OpenAI, A nine-dimensional counterexample to Borsuk's covering assertion (result family 156)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BorsukNine.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A nine-dimensional counterexample to Borsuk's covering assertion (result family 156)*, OpenAI Math Release, September 23, 2026, result family 156, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BorsukNine.Admissible.face_extends_three` of [lean/OAI/Geometry/Borsuk/Support/SupportIncidence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Borsuk/Support/SupportIncidence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BorsukNine`, with `open Set MeasureTheory`, `open scoped RealInnerProductSpace`):
--
--   ```lean
--   lemma Admissible.face_extends_three {f : E → ι → ℝ} (hf : Admissible f)
--       (hcard : Fintype.card ι = 6) {U : Finset ι} (hU : SupportFace f U) :
--       ∃ I : Finset ι, I.card = 3 ∧ SupportFace f I ∧ U ⊆ I
--   ```
--
--   **Definitions.** The statement is written with `OAI.BorsukNine.Admissible` and `OAI.BorsukNine.SupportFace` (definitions bundle `OAIQ058B000` of this split).
--
--   **Used by.** The proof of `OAI.BorsukNine.main_theorem` of this split imports it.
-- source:
--   OpenAI, A nine-dimensional counterexample to Borsuk's covering assertion (result family 156), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 156; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-nine-dimensional-counterexample-to-Borsuks-covering-assertion-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Borsuk/Support/SupportIncidence.lean (declaration OAI.BorsukNine.Admissible.face_extends_three)

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
open scoped RealInnerProductSpace

section SixPure
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ (Fin 3)

lemma Admissible.face_extends_three {f : E → ι → ℝ} (hf : Admissible f)
    (hcard : Fintype.card ι = 6) {U : Finset ι} (hU : SupportFace f U) :
    ∃ I : Finset ι, I.card = 3 ∧ SupportFace f I ∧ U ⊆ I := by
  sorry

end SixPure

end BorsukNine

end OAI
end
