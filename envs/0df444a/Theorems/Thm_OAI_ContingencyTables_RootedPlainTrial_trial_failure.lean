-- Prove2me | Theorems.Thm_OAI_ContingencyTables_RootedPlainTrial_trial_failure
-- name    : OAI.ContingencyTables.RootedPlainTrial.trial_failure
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T03:22:05.884173+00:00
-- url     : https://prove2.me/theorems/8a895df8-813b-4175-b49c-a909e96c074d
-- title:
--   OAI.ContingencyTables.RootedPlainTrial.trial_failure: intermediate lemma from OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContingencyTables.RootedPlainTrial.trial_failure` of [lean/OAI/Combinatorics/ContingencyTables/Rooted/RootedPlainTrial.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Rooted/RootedPlainTrial.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContingencyTables.RootedPlainTrial`, with `open CommonBasesFPRAS FirstSuccess ResidualMixture RealKernelApproximation`, `open CompanionFactorialApplication CompanionRationalUpdates CompanionOracleDensity`, `open RootedAnnealing RootedWarmStart RootedPhaseTrial`, `open CompanionPhaseWords (Stored)`, `open CompanionConcentration (pairs_ne_nil)`, `open CompanionTraceWords (eventIndicator)`, `open TwoLiftStates GridBoundary`, `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem trial_failure (A : Instance I J) (R : RootedCompletion.Selection A.T)
--       (C : ℕ) (hC : 0 < C) (K j k N : ℕ)
--       (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
--       (hj : j+1 ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi ≤ 1/4)
--       (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
--       (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
--       (v : Grid (I := Fin (dimension A)) K) (hp : 0 < Fintype.card (Labels A))
--       (old : Stored A) (hw : ∀ p q,0 < old.multiplier p q) (hE : 0 < old.estimate)
--       (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (old.multiplier p q:ℝ)))
--       (p : RationalLaw (PlainIndex (pairs : List (Pair A))))
--       (q : PlainIndex (pairs : List (Pair A)) → ℝ)
--       (hq : ∀ S,0 ≤ q S) (hq1 : ∑ S,q S ≤ 1)
--       (hwarm : ∀ S,q S ≤ 2*law A R j S.val.val)
--       (eta : ℝ) (he0 : 0 < eta) (he1 : eta ≤ 1/4) :
--       (∑ S,(p.mass S:ℝ)*uniformAverage (fun bits : TrialWords A C K j k N xi =>
--         eventIndicator (¬∃ next,trial A R C K j k N hK hW xi v old S.val bits=some next ∧
--           ValidOutput A R j old xi eta next))) ≤
--         32000*(Fintype.card (Labels A):ℝ)^8*
--           ObservableBounds.observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)/
--             (((N+1:ℕ):ℝ)*eta^2)+
--           (N:ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2)+
--             2*distance (fun S => (p.mass S:ℝ)) q+2*((N+1:ℕ):ℝ)*(xi:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CommonBasesFPRAS.ChainIndex`, `OAI.CommonBasesFPRAS.ChainState`, `OAI.CommonBasesFPRAS.GoodMultipliers`, `OAI.CommonBasesFPRAS.PlainIndex`, `OAI.CommonBasesFPRAS.PlainState` and `OAI.CommonBasesFPRAS.uniformAverage` (definitions bundle `OAIQ089A000` of this split); `OAI.ContingencyTables.CompanionFactorialApplication.Instance`, `OAI.ContingencyTables.CompanionFactorialApplication.Labels`, `OAI.ContingencyTables.CompanionFactorialApplication.SmallCell`, `OAI.ContingencyTables.CompanionOracleDensity.binWidth`, `OAI.ContingencyTables.CompanionOracleDensity.dimension`, `OAI.ContingencyTables.CompanionOracleDensity.rationalHeight`, `OAI.ContingencyTables.CompanionPhaseWords.Stored`, `OAI.ContingencyTables.CompanionRationalUpdates.Pair`, `OAI.ContingencyTables.CompanionTraceWords.eventIndicator`, `OAI.ContingencyTables.GridBoundary.Grid`, `OAI.ContingencyTables.ResidualMixture.RationalLaw`, `OAI.ContingencyTables.RootedCompletion.Selection` and `OAI.ContingencyTables.TwoLiftStates.pairs` (definitions bundle `OAIQ089A001` of this split); `OAI.ContingencyTables.ObservableBounds.observableConstant` and `OAI.ContingencyTables.RealKernelApproximation.distance` (definitions bundle `OAIQ089A002` of this split); `OAI.ContingencyTables.CompanionBooleanPhase.stepBits` (definitions bundle `OAIQ089A003` of this split); `OAI.ContingencyTables.PublishedInputs.FiniteBoxPrekopaLeindler` and `OAI.ContingencyTables.PublishedInputs.FiniteCheeger` (definitions bundle `OAIQ089A004` of this split); `OAI.ContingencyTables.CompanionPhaseWords.phaseBits`, `OAI.ContingencyTables.RootedPhaseTrial.TrialWords` and `OAI.ContingencyTables.RootedPhaseTrial.trial` (definitions bundle `OAIQ089A006` of this split); `OAI.ContingencyTables.RootedAnnealing.weight`, `OAI.ContingencyTables.RootedPhaseTrial.ValidOutput` and `OAI.ContingencyTables.RootedWarmStart.law` (definitions bundle `OAIQ089A008` of this split).
--
--   **Used by.** The proof of `OAI.ContingencyTables.RootedHistoryConfidence.history_success` of this split imports it.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Rooted/RootedPlainTrial.lean (declaration OAI.ContingencyTables.RootedPlainTrial.trial_failure)

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

namespace ContingencyTables.RootedPlainTrial

open CommonBasesFPRAS FirstSuccess ResidualMixture RealKernelApproximation
open CompanionFactorialApplication CompanionRationalUpdates CompanionOracleDensity
open RootedAnnealing RootedWarmStart RootedPhaseTrial
open CompanionPhaseWords (Stored)
open CompanionConcentration (pairs_ne_nil)
open CompanionTraceWords (eventIndicator)
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

theorem trial_failure (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C : ℕ) (hC : 0 < C) (K j k N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j+1 ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi ≤ 1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0 < Fintype.card (Labels A))
    (old : Stored A) (hw : ∀ p q,0 < old.multiplier p q) (hE : 0 < old.estimate)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (old.multiplier p q:ℝ)))
    (p : RationalLaw (PlainIndex (pairs : List (Pair A))))
    (q : PlainIndex (pairs : List (Pair A)) → ℝ)
    (hq : ∀ S,0 ≤ q S) (hq1 : ∑ S,q S ≤ 1)
    (hwarm : ∀ S,q S ≤ 2*law A R j S.val.val)
    (eta : ℝ) (he0 : 0 < eta) (he1 : eta ≤ 1/4) :
    (∑ S,(p.mass S:ℝ)*uniformAverage (fun bits : TrialWords A C K j k N xi =>
      eventIndicator (¬∃ next,trial A R C K j k N hK hW xi v old S.val bits=some next ∧
        ValidOutput A R j old xi eta next))) ≤
      32000*(Fintype.card (Labels A):ℝ)^8*
        ObservableBounds.observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)/
          (((N+1:ℕ):ℝ)*eta^2)+
        (N:ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2)+
          2*distance (fun S => (p.mass S:ℝ)) q+2*((N+1:ℕ):ℝ)*(xi:ℝ) := by
  sorry

end
end ContingencyTables.RootedPlainTrial

end OAI
end
