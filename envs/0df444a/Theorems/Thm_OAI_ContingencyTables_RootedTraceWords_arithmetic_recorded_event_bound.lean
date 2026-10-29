-- Prove2me | Theorems.Thm_OAI_ContingencyTables_RootedTraceWords_arithmetic_recorded_event_bound
-- name    : OAI.ContingencyTables.RootedTraceWords.arithmetic_recorded_event_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T03:21:41.421008+00:00
-- url     : https://prove2.me/theorems/e51a25f6-5a50-4511-8d1c-1c20e23f32e4
-- title:
--   OAI.ContingencyTables.RootedTraceWords.arithmetic_recorded_event_bound: intermediate lemma from OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContingencyTables.RootedTraceWords.arithmetic_recorded_event_bound` of [lean/OAI/Combinatorics/ContingencyTables/Rooted/RootedTraceWords.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Rooted/RootedTraceWords.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContingencyTables.RootedTraceWords`, with `open CommonBasesFPRAS CompanionFactorialApplication RootedBooleanPhase`, `open CompanionOracleDensity CompanionWeightOracle`, `open CompanionRationalUpdates TwoLiftStates GridBoundary FirstSuccess ResidualMixture`, `open CompanionBooleanPhase (State stepBits slowdown slowdown_bounds)`, `open CompanionPhaseTrajectory (historyPrefix)`, `open CompanionTraceWords (eventIndicator firstHit )`, `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem arithmetic_recorded_event_bound (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0<C) (K j k : ℕ)
--       (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
--       (hj : j ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
--       (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
--       (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
--       (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
--       (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) (N : ℕ) (S : State A)
--       (E : List (State A) → Prop) :
--       uniformAverage (fun bits : Fin (N*stepBits A C K j k xi) → Bool =>
--         eventIndicator (E (historyPrefix
--           (RootedArithmeticStep.recordedWalk A R C K j k N N hK hW xi v w S bits))))≤
--         (targetChain A R j hp w hw).pathExpectation N S (fun xs => eventIndicator (E xs))+
--         N*((6*(xi:ℝ)+1/(2:ℝ)^k)/2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CommonBasesFPRAS.ChainState`, `OAI.CommonBasesFPRAS.uniformAverage` and `OAI.CommonBasesFPRAS.FiniteChain.pathExpectation` (definitions bundle `OAIQ089A000` of this split); `OAI.ContingencyTables.CompanionFactorialApplication.Instance`, `OAI.ContingencyTables.CompanionFactorialApplication.Labels`, `OAI.ContingencyTables.CompanionFactorialApplication.SmallCell`, `OAI.ContingencyTables.CompanionOracleDensity.binWidth`, `OAI.ContingencyTables.CompanionOracleDensity.dimension`, `OAI.ContingencyTables.CompanionOracleDensity.rationalHeight`, `OAI.ContingencyTables.CompanionPhaseTrajectory.historyPrefix`, `OAI.ContingencyTables.CompanionRationalUpdates.Pair`, `OAI.ContingencyTables.CompanionTraceWords.eventIndicator`, `OAI.ContingencyTables.GridBoundary.Grid`, `OAI.ContingencyTables.RootedCompletion.Selection` and `OAI.ContingencyTables.TwoLiftStates.pairs` (definitions bundle `OAIQ089A001` of this split); `OAI.ContingencyTables.CompanionBooleanPhase.State` and `OAI.ContingencyTables.CompanionBooleanPhase.stepBits` (definitions bundle `OAIQ089A003` of this split); `OAI.ContingencyTables.PublishedInputs.FiniteBoxPrekopaLeindler` and `OAI.ContingencyTables.PublishedInputs.FiniteCheeger` (definitions bundle `OAIQ089A004` of this split); `OAI.ContingencyTables.RootedArithmeticStep.recordedWalk` (definitions bundle `OAIQ089A006` of this split); `OAI.ContingencyTables.RootedBooleanPhase.targetChain` (definitions bundle `OAIQ089A008` of this split).
--
--   **Used by.** The proofs of `OAI.ContingencyTables.RootedHistoryConfidence.history_success` and `OAI.ContingencyTables.RootedObservationStart.observed_failure_near` of this split import it.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Rooted/RootedTraceWords.lean (declaration OAI.ContingencyTables.RootedTraceWords.arithmetic_recorded_event_bound)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ089A006
import Definitions.Def_OAIQ089A008

section

attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ContingencyTables.RootedTraceWords

open CommonBasesFPRAS CompanionFactorialApplication RootedBooleanPhase
open CompanionOracleDensity CompanionWeightOracle
open CompanionRationalUpdates TwoLiftStates GridBoundary FirstSuccess ResidualMixture
open CompanionBooleanPhase (State stepBits slowdown slowdown_bounds)
open CompanionPhaseTrajectory (historyPrefix)
open CompanionTraceWords (eventIndicator firstHit )
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

theorem arithmetic_recorded_event_bound (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0<C) (K j k : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) (N : ℕ) (S : State A)
    (E : List (State A) → Prop) :
    uniformAverage (fun bits : Fin (N*stepBits A C K j k xi) → Bool =>
      eventIndicator (E (historyPrefix
        (RootedArithmeticStep.recordedWalk A R C K j k N N hK hW xi v w S bits))))≤
      (targetChain A R j hp w hw).pathExpectation N S (fun xs => eventIndicator (E xs))+
      N*((6*(xi:ℝ)+1/(2:ℝ)^k)/2) := by
  sorry

end
end ContingencyTables.RootedTraceWords

end OAI
end
