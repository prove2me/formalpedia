-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_Computability_deletion_increment_linear_sat
-- name    : OAI.FixedClauseThreshold.Computability.deletion_increment_linear_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:26:37.193511+00:00
-- url     : https://prove2.me/theorems/54777aa2-2355-4d94-8517-ed953e82757d
-- title:
--   OAI.FixedClauseThreshold.Computability.deletion_increment_linear_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.FixedClauseThreshold.Computability.deletion_increment_linear` of [lean/OAI/Probability/SATComputability/DeletionScaling.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SATComputability/DeletionScaling.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.FixedClauseThreshold.Computability`, with `open DilutedSpinGlass Filter`, `open scoped NNReal Topology`):
--
--   ```lean
--   theorem deletion_increment_linear_sat (n q : ℕ) [NeZero n] (hq : 0 < q) :
--       let P := FiniteLaw.pi (fun _ : Fin (20*n) => candidateBlock (n := n) 1 3 Finset.univ)
--       P.expect (maskLifetime (20*n) (deletionBudgetMask n (n/q))) -
--         P.expect (maskLifetime (20*n) (deletionBudgetMask n 0)) ≤ deletionSlope q*n
--   ```
--
--   **Definitions.** The statement is written with `OAI.FixedClauseThreshold.Computability.DeletionCandidate` (definitions bundle `OAIQ067A000` of this split); `OAI.FixedClauseThreshold.Computability.deletionSlope` (definitions bundle `OAIQ067A001` of this split); `OAI.FixedClauseThreshold.Computability.candidateBlock`, `OAI.FixedClauseThreshold.Computability.deletionBudgetMask` and `OAI.FixedClauseThreshold.Computability.maskLifetime` (definitions bundle `OAIQ067A002` of this split); `OAI.DilutedSpinGlass.FiniteLaw`, `OAI.DilutedSpinGlass.FiniteLaw.expect` and `OAI.DilutedSpinGlass.FiniteLaw.pi` (the published bundle `Def_OAIQ041D000`).
--
--   **Used by.** The proof of `OAI.FixedClauseThreshold.Computability.threshold_program_sat` of this split imports it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SATComputability/DeletionScaling.lean (declaration OAI.FixedClauseThreshold.Computability.deletion_increment_linear)

import Mathlib
import Definitions.Def_OAIQ041D000
import Definitions.Def_OAIQ067A002

section

attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Filter
open scoped NNReal Topology

theorem deletion_increment_linear_sat (n q : ℕ) [NeZero n] (hq : 0 < q) :
    let P := FiniteLaw.pi (fun _ : Fin (20*n) => candidateBlock (n := n) 1 3 Finset.univ)
    P.expect (maskLifetime (20*n) (deletionBudgetMask n (n/q))) -
      P.expect (maskLifetime (20*n) (deletionBudgetMask n 0)) ≤ deletionSlope q*n := by
  sorry

end FixedClauseThreshold.Computability

end OAI
end
