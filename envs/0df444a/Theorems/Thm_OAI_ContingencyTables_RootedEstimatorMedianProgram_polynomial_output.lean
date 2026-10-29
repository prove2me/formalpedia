-- Prove2me | Theorems.Thm_OAI_ContingencyTables_RootedEstimatorMedianProgram_polynomial_output
-- name    : OAI.ContingencyTables.RootedEstimatorMedianProgram.polynomial_output
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T03:18:47.068739+00:00
-- url     : https://prove2.me/theorems/3305d2e6-62e0-4b77-bec1-dc9300b029ac
-- title:
--   OAI.ContingencyTables.RootedEstimatorMedianProgram.polynomial_output: intermediate lemma from OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContingencyTables.RootedEstimatorMedianProgram.polynomial_output` of [lean/OAI/Combinatorics/ContingencyTables/Rooted/RootedEstimatorMedianProgram.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Rooted/RootedEstimatorMedianProgram.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContingencyTables.RootedEstimatorMedianProgram`, with `open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms`, `open RootedEstimatorLayoutProgram`):
--
--   ```lean
--   theorem polynomial_output : PolynomialTime outputRealizer
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatchingFPRAS.TreeTyped.instCodecBool`, `OAI.MatchingFPRAS.TreeTyped.instCodecList`, `OAI.MatchingFPRAS.TreeTyped.instCodecNat` and `OAI.MatchingFPRAS.TreeTyped.instCodecProd` (definitions bundle `OAIQ089A000` of this split); `OAI.ContingencyTables.DensePrograms.MatrixCode`, `OAI.ContingencyTables.FiniteGraphRootProgram.GraphCode`, `OAI.ContingencyTables.RootedDemandProgram.Input`, `OAI.ContingencyTables.RootedEstimatorLayoutProgram.Context`, `OAI.ContingencyTables.RootedEstimatorLayoutProgram.Schedule`, `OAI.ContingencyTables.RootedEstimatorLayoutProgram.State`, `OAI.ContingencyTables.RootedForestCatalog.Data`, `OAI.ContingencyTables.RootedOracleWalkProgram.Frame`, `OAI.ContingencyTables.RootedPenaltyEvaluateProgram.Parameters` and `OAI.MatchingFPRAS.TreeFraction.Fraction` (definitions bundle `OAIQ089A001` of this split); `OAI.ContingencyTables.RootedEstimatorMedianProgram.Input` and `OAI.ContingencyTables.RootedEstimatorMedianProgram.output` (definitions bundle `OAIQ089A003` of this split); `OAI.ContingencyTables.RootedEstimatorMedianProgram.outputRealizer` (definitions bundle `OAIQ089A006` of this split); `OAI.MatchingFPRAS.TreeTyped.PolynomialTime` (definitions bundle `OAIQ089A008` of this split).
--
--   **Used by.** The proofs of `OAI.ContingencyTables.CompanionObservationQueriesProgram.polynomial_output`, `OAI.ContingencyTables.CompanionPhaseTrialProgram.polynomial_output`, `OAI.ContingencyTables.CompanionRepeatedReturnProgram.polynomial_output` and `OAI.ContingencyTables.CountingBranchProgram.polynomial_publicOutput` of this split import it.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Rooted/RootedEstimatorMedianProgram.lean (declaration OAI.ContingencyTables.RootedEstimatorMedianProgram.polynomial_output)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ089A006
import Definitions.Def_OAIQ089A008

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ContingencyTables.RootedEstimatorMedianProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
open RootedEstimatorLayoutProgram

attribute [local irreducible] samples

theorem polynomial_output : PolynomialTime outputRealizer := by
  sorry

open GridBoundary CommonBasesFPRAS
open scoped Classical

end ContingencyTables.RootedEstimatorMedianProgram

end OAI
end
