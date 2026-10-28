-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_Computability_restored_process_moment_sat
-- name    : OAI.FixedClauseThreshold.Computability.restored_process_moment_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:27:06.493997+00:00
-- url     : https://prove2.me/theorems/6e9458ac-b8b8-4355-9b49-0b54322fd625
-- title:
--   OAI.FixedClauseThreshold.Computability.restored_process_moment_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.FixedClauseThreshold.Computability.restored_process_moment` of [lean/OAI/Probability/SATComputability/RestoredProcessMoment.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SATComputability/RestoredProcessMoment.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.FixedClauseThreshold.Computability`, with `open DilutedSpinGlass`, `open scoped Classical NNReal`):
--
--   ```lean
--   theorem restored_process_moment_sat {n : ℕ} [NeZero n] (M r : ℕ)
--       (rate : ℝ≥0) (hrate : (1 : ℝ)/8 ≤ rate)
--       (P : FiniteLaw (Fin M → Finset (DeletionCandidate n))) (ε : ℝ)
--       (hP : ∀ U, (finiteMap P frontloadMask).expect
--         (fun I => if U ∩ I = ∅ then 1 else 0) ≤ poissonKillProbability U 2 60 + ε) :
--       P.expect (fun f => P.expect (fun t =>
--         (FiniteLaw.pi (fun _ : Fin M => candidateBlock rate 3 Finset.univ)).expect (fun base =>
--           (maskLifetime M (deletionBudgetMask n r) base -
--             maskLifetime M (deletionBudgetMask (n+1) r)
--               (fun j => restoredMask (base j) (f j) (t j)))^(6/5 : ℝ)))) ≤
--         (48/5 : ℝ)*(∑' j, dyadicMomentCoefficient j) +
--           (12/5 : ℝ)*ε^2*(M : ℝ)^(6/5 : ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.FixedClauseThreshold.Computability.DeletionCandidate` (definitions bundle `OAIQ067A000` of this split); `OAI.FixedClauseThreshold.Computability.dyadicMomentCoefficient` and `OAI.FixedClauseThreshold.Computability.finiteMap` (definitions bundle `OAIQ067A001` of this split); `OAI.FixedClauseThreshold.Computability.candidateBlock`, `OAI.FixedClauseThreshold.Computability.deletionBudgetMask`, `OAI.FixedClauseThreshold.Computability.frontloadMask`, `OAI.FixedClauseThreshold.Computability.maskLifetime`, `OAI.FixedClauseThreshold.Computability.poissonKillProbability` and `OAI.FixedClauseThreshold.Computability.restoredMask` (definitions bundle `OAIQ067A002` of this split); `OAI.DilutedSpinGlass.FiniteLaw`, `OAI.DilutedSpinGlass.FiniteLaw.expect` and `OAI.DilutedSpinGlass.FiniteLaw.pi` (the published bundle `Def_OAIQ041D000`).
--
--   **Used by.** The proof of `OAI.FixedClauseThreshold.Computability.deletion_increment_linear_sat` of this split imports it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SATComputability/RestoredProcessMoment.lean (declaration OAI.FixedClauseThreshold.Computability.restored_process_moment)

import Mathlib
import Definitions.Def_OAIQ041D000
import Definitions.Def_OAIQ067A002

section

attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped Classical NNReal

theorem restored_process_moment_sat {n : ℕ} [NeZero n] (M r : ℕ)
    (rate : ℝ≥0) (hrate : (1 : ℝ)/8 ≤ rate)
    (P : FiniteLaw (Fin M → Finset (DeletionCandidate n))) (ε : ℝ)
    (hP : ∀ U, (finiteMap P frontloadMask).expect
      (fun I => if U ∩ I = ∅ then 1 else 0) ≤ poissonKillProbability U 2 60 + ε) :
    P.expect (fun f => P.expect (fun t =>
      (FiniteLaw.pi (fun _ : Fin M => candidateBlock rate 3 Finset.univ)).expect (fun base =>
        (maskLifetime M (deletionBudgetMask n r) base -
          maskLifetime M (deletionBudgetMask (n+1) r)
            (fun j => restoredMask (base j) (f j) (t j)))^(6/5 : ℝ)))) ≤
      (48/5 : ℝ)*(∑' j, dyadicMomentCoefficient j) +
        (12/5 : ℝ)*ε^2*(M : ℝ)^(6/5 : ℝ) := by
  sorry

end FixedClauseThreshold.Computability

end OAI
end
