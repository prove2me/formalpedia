-- Prove2me | Theorems.Thm_OAI_ContingencyTables_ExactGatePublic_failure
-- name    : OAI.ContingencyTables.ExactGatePublic.failure
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T03:31:34.070171+00:00
-- url     : https://prove2.me/theorems/aa148890-eaef-45d4-af96-f0274e4dd024
-- title:
--   OAI.ContingencyTables.ExactGatePublic.failure: intermediate lemma from OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContingencyTables.ExactGatePublic.failure` of [lean/OAI/Combinatorics/ContingencyTables/Sampling/ExactGatePublic.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Sampling/ExactGatePublic.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContingencyTables.ExactGatePublic`, with `open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing`, `open DensePrograms ProfilePrograms SmallGraphProfiles`, `open ExactTablePrefix (code decode input)`, `open scoped BigOperators Classical`):
--
--   ```lean
--   lemma failure (htotal : (∑ i,r i)=∑ j,c j) :
--       (experiment r c).mean (fun o => if o=none then 1 else 0)=1/(2:ℚ)^(correctionPrecision r c)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatchingFPRAS.PhysicalStream.Experiment.mean` (definitions bundle `OAIQ089A002` of this split); `OAI.ContingencyTables.SmallGraphProfiles.correctionPrecision` (definitions bundle `OAIQ089A007` of this split); `OAI.ContingencyTables.ExactGatePublic.experiment` (definitions bundle `OAIQ089A009` of this split); `OAI.ContingencyTables.Table` (the published bundle `Def_ContingencyTables`).
--
--   **Used by.** The proof of `OAI.ContingencyTables.exactSampling` of this split imports it.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Sampling/ExactGatePublic.lean (declaration OAI.ContingencyTables.ExactGatePublic.failure)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_ContingencyTables
import Definitions.Def_OAIQ089A009

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ContingencyTables.ExactGatePublic
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing
open DensePrograms ProfilePrograms SmallGraphProfiles
open ExactTablePrefix (code decode input)
open scoped BigOperators Classical
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

attribute [local irreducible] exactOrdinary

lemma failure (htotal : (∑ i,r i)=∑ j,c j) :
    (experiment r c).mean (fun o => if o=none then 1 else 0)=1/(2:ℚ)^(correctionPrecision r c) := by
  sorry

end
end ContingencyTables.ExactGatePublic

end OAI
end
