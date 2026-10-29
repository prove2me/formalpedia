-- Prove2me | Theorems.Thm_OAI_ContingencyTables_RootedObservationStart_observed_failure_near
-- name    : OAI.ContingencyTables.RootedObservationStart.observed_failure_near
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T03:18:55.775984+00:00
-- url     : https://prove2.me/theorems/34a44a11-26f8-4b80-b510-c0637eddbe08
-- title:
--   OAI.ContingencyTables.RootedObservationStart.observed_failure_near: intermediate lemma from OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContingencyTables.RootedObservationStart.observed_failure_near` of [lean/OAI/Combinatorics/ContingencyTables/Rooted/RootedObservationStart.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Rooted/RootedObservationStart.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContingencyTables.RootedObservationStart`, with `open CommonBasesFPRAS RealKernelApproximation CompanionFactorialApplication`, `open CompanionRationalUpdates CompanionOracleDensity RootedAnnealing RootedMultiplierUpdate`, `open RootedPhaseExperiment RootedPhaseWords`, `open CompanionBooleanPhase (State stepBits)`, `open CompanionPhaseWords (phaseBits Stored)`, `open CompanionTraceWords (eventIndicator)`, `open TwoLiftStates GridBoundary`, `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem observed_failure_near (A : Instance I J) (R : RootedCompletion.Selection A.T)
--       (C : ℕ) (hC : 0 < C) (K j k N : ℕ)
--       (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
--       (hj : j ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi ≤ 1/4)
--       (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
--       (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
--       (v : Grid (I := Fin (dimension A)) K) (hp : 0 < Fintype.card (Labels A))
--       (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0 < w p q)
--       (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ)))
--       (p q : State A → ℝ) (hq : ∀ S,0 ≤ q S) (hmass : ∑ S,q S ≤ 1)
--       (hwarm : ∀ S,q S ≤ (10*(Fintype.card (Labels A):ℝ)^2)*
--         chainWeight pairs (fun p q => (w p q:ℝ)) (weight A R j) S.val/
--           chainTotal pairs (fun p q => (w p q:ℝ)) (weight A R j))
--       (eta : ℝ) (heta : 0 < eta) :
--       (∑ S,p S*uniformAverage (fun bits : Fin (N*stepBits A C K j k xi) → Bool =>
--         eventIndicator (¬AccuratePhase pairs (fun p q => (w p q:ℝ)) (weight A R j) (ratio A R j)
--           eta (List.ofFn (observedStates A R C K j k N hK hW xi v w S bits))))) ≤
--         32000*(Fintype.card (Labels A):ℝ)^8*
--           ObservableBounds.observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)/
--             (((N+1:ℕ):ℝ)*eta^2)+
--           (N:ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2)+2*distance p q
--   ```
--
--   **Definitions.** The statement is written with `OAI.CommonBasesFPRAS.AccuratePhase`, `OAI.CommonBasesFPRAS.ChainState`, `OAI.CommonBasesFPRAS.GoodMultipliers`, `OAI.CommonBasesFPRAS.chainTotal`, `OAI.CommonBasesFPRAS.chainWeight` and `OAI.CommonBasesFPRAS.uniformAverage` (definitions bundle `OAIQ089A000` of this split); `OAI.ContingencyTables.CompanionFactorialApplication.Instance`, `OAI.ContingencyTables.CompanionFactorialApplication.Labels`, `OAI.ContingencyTables.CompanionFactorialApplication.SmallCell`, `OAI.ContingencyTables.CompanionOracleDensity.binWidth`, `OAI.ContingencyTables.CompanionOracleDensity.dimension`, `OAI.ContingencyTables.CompanionOracleDensity.rationalHeight`, `OAI.ContingencyTables.CompanionRationalUpdates.Pair`, `OAI.ContingencyTables.CompanionTraceWords.eventIndicator`, `OAI.ContingencyTables.GridBoundary.Grid`, `OAI.ContingencyTables.RootedCompletion.Selection` and `OAI.ContingencyTables.TwoLiftStates.pairs` (definitions bundle `OAIQ089A001` of this split); `OAI.ContingencyTables.ObservableBounds.observableConstant` and `OAI.ContingencyTables.RealKernelApproximation.distance` (definitions bundle `OAIQ089A002` of this split); `OAI.ContingencyTables.CompanionBooleanPhase.State` and `OAI.ContingencyTables.CompanionBooleanPhase.stepBits` (definitions bundle `OAIQ089A003` of this split); `OAI.ContingencyTables.PublishedInputs.FiniteBoxPrekopaLeindler` and `OAI.ContingencyTables.PublishedInputs.FiniteCheeger` (definitions bundle `OAIQ089A004` of this split); `OAI.ContingencyTables.RootedPhaseExperiment.observedStates` (definitions bundle `OAIQ089A006` of this split); `OAI.ContingencyTables.RootedAnnealing.weight` and `OAI.ContingencyTables.RootedMultiplierUpdate.ratio` (definitions bundle `OAIQ089A008` of this split).
--
--   **Used by.** The proof of `OAI.ContingencyTables.RootedPlainTrial.trial_failure` of this split imports it.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Rooted/RootedObservationStart.lean (declaration OAI.ContingencyTables.RootedObservationStart.observed_failure_near)

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

namespace ContingencyTables.RootedObservationStart

open CommonBasesFPRAS RealKernelApproximation CompanionFactorialApplication
open CompanionRationalUpdates CompanionOracleDensity RootedAnnealing RootedMultiplierUpdate
open RootedPhaseExperiment RootedPhaseWords
open CompanionBooleanPhase (State stepBits)
open CompanionPhaseWords (phaseBits Stored)
open CompanionTraceWords (eventIndicator)
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]

theorem observed_failure_near (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C : ℕ) (hC : 0 < C) (K j k N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi ≤ 1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0 < Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0 < w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ)))
    (p q : State A → ℝ) (hq : ∀ S,0 ≤ q S) (hmass : ∑ S,q S ≤ 1)
    (hwarm : ∀ S,q S ≤ (10*(Fintype.card (Labels A):ℝ)^2)*
      chainWeight pairs (fun p q => (w p q:ℝ)) (weight A R j) S.val/
        chainTotal pairs (fun p q => (w p q:ℝ)) (weight A R j))
    (eta : ℝ) (heta : 0 < eta) :
    (∑ S,p S*uniformAverage (fun bits : Fin (N*stepBits A C K j k xi) → Bool =>
      eventIndicator (¬AccuratePhase pairs (fun p q => (w p q:ℝ)) (weight A R j) (ratio A R j)
        eta (List.ofFn (observedStates A R C K j k N hK hW xi v w S bits))))) ≤
      32000*(Fintype.card (Labels A):ℝ)^8*
        ObservableBounds.observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)/
          (((N+1:ℕ):ℝ)*eta^2)+
        (N:ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2)+2*distance p q := by
  sorry

end
end ContingencyTables.RootedObservationStart

end OAI
end
