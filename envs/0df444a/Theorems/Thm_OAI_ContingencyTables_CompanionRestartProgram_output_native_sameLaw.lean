-- Prove2me | Theorems.Thm_OAI_ContingencyTables_CompanionRestartProgram_output_native_sameLaw
-- name    : OAI.ContingencyTables.CompanionRestartProgram.output_native_sameLaw
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T03:16:21.979992+00:00
-- url     : https://prove2.me/theorems/f53d05f3-c8d5-4272-b4ef-0e93c67cd802
-- title:
--   OAI.ContingencyTables.CompanionRestartProgram.output_native_sameLaw: intermediate lemma from OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContingencyTables.CompanionRestartProgram.output_native_sameLaw` of [lean/OAI/Combinatorics/ContingencyTables/Counting/CompanionRestartNativeLaw.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Counting/CompanionRestartNativeLaw.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContingencyTables.CompanionRestartProgram`, with `open MatchingFPRAS CommonBasesFPRAS FirstSuccess FiniteObservableTransport`, `open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal`, `open CompanionArithmeticProposal CompanionEvaluatedWeightProgram`, `open CompanionOracleDensity TwoLiftStates GridBoundary`, `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem output_native_sameLaw (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
--       (hC : 0 < C) (hH : j ≤ rationalHeight A C) (hK : 1 ≤ K)
--       (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
--       (parameters : CountingPhaseParametersProgram.Input)
--       (hxi : 0 < TreeFraction.val (CountingPhaseParametersProgram.noise parameters))
--       (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
--       (reserve : List Bool)
--       (hdegree : ∀ i : Fin j,RootedOracleConfigProgram.rootDegree
--         (CompanionRestartStageProgram.oracleData A C K (i.val+1) parameters z v reserve) ≤ reserve.length)
--       (hdepth : ∀ i : Fin j,RootedOracleConfigProgram.depth
--         (CompanionRestartStageProgram.oracleData A C K (i.val+1) parameters z v reserve) ≤ reserve.length)
--       (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction)
--       (S : PlainIndex (pairs : List (CompanionRationalUpdates.Pair A))) :
--       SameLaw (fun bits : Fin (sumBits A C K j parameters) → Bool =>
--         output (baseData A C K j parameters z v reserve w S.val.val,List.ofFn bits))
--         (fun bits : Fin (sumBits A C K j parameters) → Bool =>
--           encodeSet (coordinateOrder A)
--             (varyingWalk (sourceWidth A C K parameters) (sourceStep A C K parameters hK hW v w) S j
--               (varyingWordEquiv (sourceWidth A C K parameters) j bits)).val.val)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CommonBasesFPRAS.ChainIndex`, `OAI.CommonBasesFPRAS.ChainState`, `OAI.CommonBasesFPRAS.PlainIndex` and `OAI.CommonBasesFPRAS.PlainState` (definitions bundle `OAIQ089A000` of this split); `OAI.ContingencyTables.CanonicalInitialEncoding.pairOrder`, `OAI.ContingencyTables.CompanionArithmeticProposal.encodeSet`, `OAI.ContingencyTables.CompanionCellCatalog.catalog`, `OAI.ContingencyTables.CompanionCellCatalog.input`, `OAI.ContingencyTables.CompanionComputedInitial.capacities`, `OAI.ContingencyTables.CompanionComputedInitial.coordinateOrder`, `OAI.ContingencyTables.CompanionFactorialApplication.Instance`, `OAI.ContingencyTables.CompanionFactorialApplication.Labels`, `OAI.ContingencyTables.CompanionFactorialApplication.SmallCell`, `OAI.ContingencyTables.CompanionFactorialApplication.View`, `OAI.ContingencyTables.CompanionOracleDensity.binWidth`, `OAI.ContingencyTables.CompanionOracleDensity.rationalHeight`, `OAI.ContingencyTables.CompanionRestartProgram.Stage`, `OAI.ContingencyTables.CountingPhaseParametersProgram.Input`, `OAI.ContingencyTables.CountingPhaseParametersProgram.noise`, `OAI.ContingencyTables.FirstSuccess.VaryingWords`, `OAI.ContingencyTables.FirstSuccess.varyingWalk`, `OAI.ContingencyTables.FirstSuccess.varyingWordEquiv`, `OAI.ContingencyTables.GridBoundary.Grid`, `OAI.ContingencyTables.InitialTransversals.Copy`, `OAI.ContingencyTables.RootedCatalogGrid.freeCount`, `OAI.ContingencyTables.TwoLiftStates.pairs`, `OAI.MatchingFPRAS.TreeFraction.Fraction` and `OAI.MatchingFPRAS.TreeFraction.val` (definitions bundle `OAIQ089A001` of this split); `OAI.ContingencyTables.FiniteObservableTransport.SameLaw` (definitions bundle `OAIQ089A005` of this split); `OAI.ContingencyTables.CompanionEvaluatedWeightProgram.LabelIndex`, `OAI.ContingencyTables.CompanionRestartProgram.baseData`, `OAI.ContingencyTables.CompanionRestartProgram.output`, `OAI.ContingencyTables.CompanionRestartProgram.sourceStep`, `OAI.ContingencyTables.CompanionRestartProgram.sourceWidth`, `OAI.ContingencyTables.CompanionRestartProgram.sumBits`, `OAI.ContingencyTables.CompanionRestartStageProgram.oracleData`, `OAI.ContingencyTables.RootedOracleConfigProgram.depth` and `OAI.ContingencyTables.RootedOracleConfigProgram.rootDegree` (definitions bundle `OAIQ089A006` of this split).
--
--   **Used by.** The proof of `OAI.ContingencyTables.CountingPositiveProgram.value_source_sameLaw` of this split imports it.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Counting/CompanionRestartNativeLaw.lean (declaration OAI.ContingencyTables.CompanionRestartProgram.output_native_sameLaw)

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

namespace ContingencyTables.CompanionRestartProgram
open MatchingFPRAS CommonBasesFPRAS FirstSuccess FiniteObservableTransport
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionEvaluatedWeightProgram
open CompanionOracleDensity TwoLiftStates GridBoundary
open scoped BigOperators Classical
noncomputable section
variable {m n : ℕ}

theorem output_native_sameLaw (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hH : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (parameters : CountingPhaseParametersProgram.Input)
    (hxi : 0 < TreeFraction.val (CountingPhaseParametersProgram.noise parameters))
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (reserve : List Bool)
    (hdegree : ∀ i : Fin j,RootedOracleConfigProgram.rootDegree
      (CompanionRestartStageProgram.oracleData A C K (i.val+1) parameters z v reserve) ≤ reserve.length)
    (hdepth : ∀ i : Fin j,RootedOracleConfigProgram.depth
      (CompanionRestartStageProgram.oracleData A C K (i.val+1) parameters z v reserve) ≤ reserve.length)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (S : PlainIndex (pairs : List (CompanionRationalUpdates.Pair A))) :
    SameLaw (fun bits : Fin (sumBits A C K j parameters) → Bool =>
      output (baseData A C K j parameters z v reserve w S.val.val,List.ofFn bits))
      (fun bits : Fin (sumBits A C K j parameters) → Bool =>
        encodeSet (coordinateOrder A)
          (varyingWalk (sourceWidth A C K parameters) (sourceStep A C K parameters hK hW v w) S j
            (varyingWordEquiv (sourceWidth A C K parameters) j bits)).val.val) := by
  sorry

end
end ContingencyTables.CompanionRestartProgram

end OAI
end
