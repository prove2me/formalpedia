-- Prove2me | Theorems.Thm_OAI_SharpLogRamsey_GeometricCover_uniform_four
-- name    : OAI.SharpLogRamsey.GeometricCover.uniform_four
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:25:33.701048+00:00
-- url     : https://prove2.me/theorems/9f5e171f-5504-4b04-a4f5-505a10909aba
-- title:
--   OAI.SharpLogRamsey.GeometricCover.uniform_four: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpLogRamsey.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpLogRamsey.GeometricCover.uniform_four` of [lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Geometry/GeometricInduction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Geometry/GeometricInduction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpLogRamsey.GeometricCover`, with `open Finset Real Filter SourceScales Incidence ProjectiveDuality Validation Projection`, `open scoped Classical Topology`):
--
--   ```lean
--   lemma uniform_four : Uniform 4 7000
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpLogRamsey.GeometricCover.Uniform` (definitions bundle `OAIQ045S000` of this split).
--
--   **Used by.** The proof of `OAI.SharpLogRamsey.ActualPivot.supplied_book` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Geometry/GeometricInduction.lean (declaration OAI.SharpLogRamsey.GeometricCover.uniform_four)

import Mathlib
import Definitions.Def_OAIQ045S000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.GeometricCover
open Finset Real Filter SourceScales Incidence ProjectiveDuality Validation Projection
open scoped Classical Topology
noncomputable section

lemma uniform_four : Uniform 4 7000 := by
  sorry

end
end SharpLogRamsey.GeometricCover

end

end OAI
end
