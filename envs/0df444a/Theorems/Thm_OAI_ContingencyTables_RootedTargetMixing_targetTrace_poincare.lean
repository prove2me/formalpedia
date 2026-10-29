-- Prove2me | Theorems.Thm_OAI_ContingencyTables_RootedTargetMixing_targetTrace_poincare
-- name    : OAI.ContingencyTables.RootedTargetMixing.targetTrace_poincare
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T03:00:59.424153+00:00
-- url     : https://prove2.me/theorems/abf10198-b8d2-45e8-b699-26eda5e12d49
-- title:
--   OAI.ContingencyTables.RootedTargetMixing.targetTrace_poincare: intermediate lemma from OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContingencyTables.RootedTargetMixing.targetTrace_poincare` of [lean/OAI/Combinatorics/ContingencyTables/Rooted/RootedTargetMixing.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Rooted/RootedTargetMixing.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContingencyTables.RootedTargetMixing`, with `open CommonBasesFPRAS CompanionFactorialApplication RootedBooleanPhase RootedTargetTrace`, `open RootedTraceWords RootedAnnealing RootedWarmStart CompanionRationalUpdates TwoLiftStates`, `open DegreeCompletion ObservableBounds`, `open CompanionBooleanPhase (State slowdown slowdown_bounds)`, `open CompanionConcentration (pairs_ne_nil )`, `open CompanionTargetMixing (restartTime )`, `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem targetTrace_poincare (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ)
--       (hp : 0<Fintype.card (Labels A)) (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
--       (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ)))
--       (H : PlainIndex (pairs : List (Pair A)) → ℝ) :
--       (RootedTargetTrace.actualTrace A R j hp w hw).variance H≤
--         (2*observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2))*
--           (RootedTargetTrace.actualTrace A R j hp w hw).energy H
--   ```
--
--   **Definitions.** The statement is written with `OAI.CommonBasesFPRAS.ChainIndex`, `OAI.CommonBasesFPRAS.ChainState`, `OAI.CommonBasesFPRAS.GoodMultipliers`, `OAI.CommonBasesFPRAS.PlainIndex`, `OAI.CommonBasesFPRAS.PlainState`, `OAI.CommonBasesFPRAS.FiniteChain.energy` and `OAI.CommonBasesFPRAS.FiniteChain.variance` (definitions bundle `OAIQ089A000` of this split); `OAI.ContingencyTables.CompanionFactorialApplication.Instance`, `OAI.ContingencyTables.CompanionFactorialApplication.Labels`, `OAI.ContingencyTables.CompanionFactorialApplication.SmallCell`, `OAI.ContingencyTables.CompanionRationalUpdates.Pair`, `OAI.ContingencyTables.RootedCompletion.Selection` and `OAI.ContingencyTables.TwoLiftStates.pairs` (definitions bundle `OAIQ089A001` of this split); `OAI.ContingencyTables.ObservableBounds.observableConstant` (definitions bundle `OAIQ089A002` of this split); `OAI.ContingencyTables.RootedAnnealing.weight` and `OAI.ContingencyTables.RootedTargetTrace.actualTrace` (definitions bundle `OAIQ089A008` of this split).
--
--   **Used by.** The proof of `OAI.ContingencyTables.RootedHistoryConfidence.history_success` of this split imports it.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Rooted/RootedTargetMixing.lean (declaration OAI.ContingencyTables.RootedTargetMixing.targetTrace_poincare)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ089A008

section

attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ContingencyTables.RootedTargetMixing

open CommonBasesFPRAS CompanionFactorialApplication RootedBooleanPhase RootedTargetTrace
open RootedTraceWords RootedAnnealing RootedWarmStart CompanionRationalUpdates TwoLiftStates
open DegreeCompletion ObservableBounds
open CompanionBooleanPhase (State slowdown slowdown_bounds)
open CompanionConcentration (pairs_ne_nil )
open CompanionTargetMixing (restartTime )
open scoped BigOperators Classical

noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]

theorem targetTrace_poincare (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ)
    (hp : 0<Fintype.card (Labels A)) (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ)))
    (H : PlainIndex (pairs : List (Pair A)) → ℝ) :
    (RootedTargetTrace.actualTrace A R j hp w hw).variance H≤
      (2*observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2))*
        (RootedTargetTrace.actualTrace A R j hp w hw).energy H := by
  sorry

end
end ContingencyTables.RootedTargetMixing

end OAI
end
