-- Prove2me | Theorems.Thm_OAI_ContingencyTables_CompanionPhaseContinuation_run_sameLaw
-- name    : OAI.ContingencyTables.CompanionPhaseContinuation.run_sameLaw
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T03:12:41.997012+00:00
-- url     : https://prove2.me/theorems/8e69c2ad-63de-4d6b-abc4-794715f3fb15
-- title:
--   OAI.ContingencyTables.CompanionPhaseContinuation.run_sameLaw: intermediate lemma from OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContingencyTables.CompanionPhaseContinuation.run_sameLaw` of [lean/OAI/Combinatorics/ContingencyTables/Counting/CompanionPhaseContinuation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Counting/CompanionPhaseContinuation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContingencyTables.CompanionPhaseContinuation`, with `open MatchingFPRAS CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal`, `open CompanionArithmeticProposal CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram`, `open CompanionOracleDensity CompanionWeightOracle GridBoundary FiniteObservableTransport CommonBasesFPRAS TwoLiftStates`, `open scoped Classical`):
--
--   ```lean
--   theorem run_sameLaw (padding : ℕ) (A : Instance (Fin m) (Fin n)) (C K j k N : ℕ)
--       (hC : 0<C) (hj : j+1 ≤ rationalHeight A C) (hK : 1≤K)
--       (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
--       (xi : ℚ) (hxi : 0<xi) (z : View A→ℕ)
--       (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
--       (degree depth nextDegree nextDepth : List Bool)
--       (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
--       (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
--       (hnextDegree : nextDegree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) (j+1))))
--       (hnextDepth : nextDepth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) (j+1))))
--       (old : CompanionPhaseWords.Stored A)
--       (w : LabelIndex A→LabelIndex A→TreeFraction.Fraction) (E : TreeFraction.Fraction)
--       (hw : ∀ i j,TreeFraction.val (w i j)=old.multiplier (pair (pairLabels A i)) (pair (pairLabels A j)))
--       (hE : TreeFraction.val E=old.estimate) (S : CompanionBooleanPhase.State A) :
--       let cs := CompanionObservationQueriesProgram.phaseConfigs A C K j xi z v degree depth nextDegree nextDepth
--       SameLaw (fun bits : Fin (N*CompanionBooleanPhase.stepBits A C K j k xi+
--           ((N+1)*CompanionObservationQueriesProgram.blockWidth cs+padding))→Bool =>
--         CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length)
--           (run cs (matrixCode w,E) k N (encodeSet (coordinateOrder A) S.val) (List.ofFn bits)))
--         (fun bits : RootedPhaseTrial.TrialWords A C K j k N xi =>
--           CompanionPhaseFinishProgram.storedView A (pairLabels A)
--             ((RootedPhaseTrial.trial A (RootedCompletion.rowColumn A.T) C K j k N hK hW xi
--               (RootedCatalogGrid.gridEquiv A K v) old S bits).getD old))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CommonBasesFPRAS.ChainState` (definitions bundle `OAIQ089A000` of this split); `OAI.ContingencyTables.CanonicalInitialEncoding.copyOrder`, `OAI.ContingencyTables.CanonicalInitialEncoding.pairOrder`, `OAI.ContingencyTables.CompanionArithmeticProposal.encodeSet`, `OAI.ContingencyTables.CompanionCellCatalog.catalog`, `OAI.ContingencyTables.CompanionCellCatalog.input`, `OAI.ContingencyTables.CompanionComputedInitial.capacities`, `OAI.ContingencyTables.CompanionComputedInitial.coordinateOrder`, `OAI.ContingencyTables.CompanionComputedProposal.pairLabels`, `OAI.ContingencyTables.CompanionFactorialApplication.Instance`, `OAI.ContingencyTables.CompanionFactorialApplication.Labels`, `OAI.ContingencyTables.CompanionFactorialApplication.SmallCell`, `OAI.ContingencyTables.CompanionFactorialApplication.View`, `OAI.ContingencyTables.CompanionMultiplierMatrixProgram.FractionMatrix`, `OAI.ContingencyTables.CompanionMultiplierMatrixProgram.matrixCode`, `OAI.ContingencyTables.CompanionOracleDensity.binWidth`, `OAI.ContingencyTables.CompanionOracleDensity.dimension`, `OAI.ContingencyTables.CompanionOracleDensity.innerTolerance`, `OAI.ContingencyTables.CompanionOracleDensity.rationalHeight`, `OAI.ContingencyTables.CompanionOracleDensity.roundingTolerance`, `OAI.ContingencyTables.CompanionPhaseFinishProgram.Fraction`, `OAI.ContingencyTables.CompanionPhaseFinishProgram.storedView`, `OAI.ContingencyTables.CompanionPhaseFinishProgram.view`, `OAI.ContingencyTables.CompanionPhaseWords.Stored`, `OAI.ContingencyTables.GridBoundary.Grid`, `OAI.ContingencyTables.InitialTransversals.Copy`, `OAI.ContingencyTables.PowerOfTwoApproximation.depth`, `OAI.ContingencyTables.PowerOfTwoApproximation.rootDegree`, `OAI.ContingencyTables.RootedCatalogGrid.freeCount`, `OAI.ContingencyTables.RootedCompletion.rowColumn`, `OAI.ContingencyTables.TwoLiftStates.pair`, `OAI.ContingencyTables.TwoLiftStates.pairs`, `OAI.MatchingFPRAS.TreeFraction.Fraction` and `OAI.MatchingFPRAS.TreeFraction.val` (definitions bundle `OAIQ089A001` of this split); `OAI.ContingencyTables.CompanionBooleanPhase.State` and `OAI.ContingencyTables.CompanionBooleanPhase.stepBits` (definitions bundle `OAIQ089A003` of this split); `OAI.ContingencyTables.FiniteObservableTransport.SameLaw` (definitions bundle `OAIQ089A005` of this split); `OAI.ContingencyTables.CompanionEvaluatedWeightProgram.LabelIndex`, `OAI.ContingencyTables.CompanionObservationQueriesProgram.Config`, `OAI.ContingencyTables.CompanionObservationQueriesProgram.blockWidth`, `OAI.ContingencyTables.CompanionObservationQueriesProgram.phaseConfigs`, `OAI.ContingencyTables.CompanionPhaseContinuation.run`, `OAI.ContingencyTables.CompanionPhaseWords.phaseBits`, `OAI.ContingencyTables.RootedCatalogGrid.gridEquiv`, `OAI.ContingencyTables.RootedPhaseTrial.TrialWords` and `OAI.ContingencyTables.RootedPhaseTrial.trial` (definitions bundle `OAIQ089A006` of this split).
--
--   **Used by.** The proof of `OAI.ContingencyTables.CountingPositiveProgram.value_source_sameLaw` of this split imports it.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Counting/CompanionPhaseContinuation.lean (declaration OAI.ContingencyTables.CompanionPhaseContinuation.run_sameLaw)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ089A005
import Definitions.Def_OAIQ089A006

section

attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ContingencyTables.CompanionPhaseContinuation
open MatchingFPRAS CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram
open CompanionOracleDensity CompanionWeightOracle GridBoundary FiniteObservableTransport CommonBasesFPRAS TwoLiftStates
open scoped Classical
noncomputable section

variable {m n : ℕ}

theorem run_sameLaw (padding : ℕ) (A : Instance (Fin m) (Fin n)) (C K j k N : ℕ)
    (hC : 0<C) (hj : j+1 ≤ rationalHeight A C) (hK : 1≤K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (xi : ℚ) (hxi : 0<xi) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth nextDegree nextDepth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (hnextDegree : nextDegree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) (j+1))))
    (hnextDepth : nextDepth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) (j+1))))
    (old : CompanionPhaseWords.Stored A)
    (w : LabelIndex A→LabelIndex A→TreeFraction.Fraction) (E : TreeFraction.Fraction)
    (hw : ∀ i j,TreeFraction.val (w i j)=old.multiplier (pair (pairLabels A i)) (pair (pairLabels A j)))
    (hE : TreeFraction.val E=old.estimate) (S : CompanionBooleanPhase.State A) :
    let cs := CompanionObservationQueriesProgram.phaseConfigs A C K j xi z v degree depth nextDegree nextDepth
    SameLaw (fun bits : Fin (N*CompanionBooleanPhase.stepBits A C K j k xi+
        ((N+1)*CompanionObservationQueriesProgram.blockWidth cs+padding))→Bool =>
      CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length)
        (run cs (matrixCode w,E) k N (encodeSet (coordinateOrder A) S.val) (List.ofFn bits)))
      (fun bits : RootedPhaseTrial.TrialWords A C K j k N xi =>
        CompanionPhaseFinishProgram.storedView A (pairLabels A)
          ((RootedPhaseTrial.trial A (RootedCompletion.rowColumn A.T) C K j k N hK hW xi
            (RootedCatalogGrid.gridEquiv A K v) old S bits).getD old)) := by
  sorry

end
end ContingencyTables.CompanionPhaseContinuation

end OAI
end
