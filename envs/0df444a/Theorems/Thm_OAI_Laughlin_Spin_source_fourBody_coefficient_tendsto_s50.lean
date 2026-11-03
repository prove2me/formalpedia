-- Prove2me | Theorems.Thm_OAI_Laughlin_Spin_source_fourBody_coefficient_tendsto_s50
-- name    : OAI.Laughlin.Spin.source_fourBody_coefficient_tendsto_s50
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:47:59.988938+00:00
-- url     : https://prove2.me/theorems/2b04df8b-65e2-44fb-a36c-f7cce169af87
-- title:
--   OAI.Laughlin.Spin.source_fourBody_coefficient_tendsto_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Spin.source_fourBody_coefficient_tendsto` of [lean/OAI/Analysis/Laughlin/FourBody/CoefficientLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/CoefficientLimit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Spin`, with `open scoped Topology`, `open Filter`):
--
--   ```lean
--   theorem source_fourBody_coefficient_tendsto_s50 (r D T p j k : ℕ)
--       (hrD : r ≤ D) (hDT : D ≤ T) (hT : p+j+k=T) :
--       Tendsto (fun Q : ℕ => fourBodyCoefficient Q r D T p j k) atTop
--         (𝓝 (fourBodyLimitCoefficient r D T p j k))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Spin.fourBodyLimitCoefficient` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Spin.fourBodyCoefficient` (definitions bundle `OAIQ050L010` of this split).
--
--   **Used by.** The proofs of `OAI.Laughlin.Fock.finiteLocalFourMatrix_tendsto_s50`, `OAI.Laughlin.Spin.fourErrorEntry_tendsto_s50` and `OAI.Laughlin.Spin.limitSliceCoefficient_antisymmetric_s50` of this split import it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/CoefficientLimit.lean (declaration OAI.Laughlin.Spin.source_fourBody_coefficient_tendsto)

import Mathlib
import Definitions.Def_OAIQ050L010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem source_fourBody_coefficient_tendsto_s50 (r D T p j k : ℕ)
    (hrD : r ≤ D) (hDT : D ≤ T) (hT : p+j+k=T) :
    Tendsto (fun Q : ℕ => fourBodyCoefficient Q r D T p j k) atTop
      (𝓝 (fourBodyLimitCoefficient r D T p j k)) := by
  sorry

end Laughlin.Spin

end OAI
end
