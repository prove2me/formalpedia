-- Prove2me | Theorems.Thm_OAI_ContingencyTables_ExactGatePolynomial_public_bound
-- name    : OAI.ContingencyTables.ExactGatePolynomial.public_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T04:52:22.646028+00:00
-- url     : https://prove2.me/theorems/6bcb71e5-4044-4b00-87ee-a2fa65c57072
-- title:
--   OAI.ContingencyTables.ExactGatePolynomial.public_bound: intermediate lemma from OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContingencyTables.ExactGatePolynomial.public_bound` of [lean/OAI/Combinatorics/ContingencyTables/Sampling/ExactGatePolynomial.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Sampling/ExactGatePolynomial.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContingencyTables.ExactGatePolynomial`, with `open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream`, `open ProfilePrograms DensePrograms Polynomial`, `open Algorithms (samplingSize encodeMargins)`, `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem public_bound (print : Polynomial ℕ) : ∃ p : Polynomial ℕ,
--       ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
--         (∑ i,r i)=∑ j,c j →
--         let B := print.eval (ExactPrintCost.matrixSize (n := n) r)
--         ExactGatePublic.budget r c B B ≤ p.eval (samplingSize n r 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ContingencyTables.ExactGatePublic.budget` and `OAI.ContingencyTables.ExactPrintCost.matrixSize` (definitions bundle `OAIQ089A009` of this split); `OAI.ContingencyTables.Algorithms.samplingSize` (the published bundle `Def_ContingencyTables`).
--
--   **Used by.** The proof of `OAI.ContingencyTables.exactSampling` of this split imports it.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Sampling/ExactGatePolynomial.lean (declaration OAI.ContingencyTables.ExactGatePolynomial.public_bound)

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

namespace ContingencyTables.ExactGatePolynomial
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream
open ProfilePrograms DensePrograms Polynomial
open Algorithms (samplingSize encodeMargins)
open scoped BigOperators Classical
noncomputable section

attribute [local irreducible] ExactTypedProgram.program exactParsedMargins
  ExactGatePrefix.budget ExactGateCost.measure

theorem public_bound (print : Polynomial ℕ) : ∃ p : Polynomial ℕ,
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
      (∑ i,r i)=∑ j,c j →
      let B := print.eval (ExactPrintCost.matrixSize (n := n) r)
      ExactGatePublic.budget r c B B ≤ p.eval (samplingSize n r 0) := by
  sorry

end
end ContingencyTables.ExactGatePolynomial

end OAI
end
