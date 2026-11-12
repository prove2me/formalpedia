-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCoupledLoop_run_initial_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.run_initial_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:12:54.315198+00:00
-- url     : https://prove2.me/theorems/f7aca811-0829-48ef-9fab-7de1c12a0ade
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.run_initial_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.run_initial` of [lean/OAI/Combinatorics/KMedianRecovery/Machines/InitialLoop.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/InitialLoop.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop`, with `open WordOperations WordList BinaryArithmetic RationalLeaves RationalHeight CanonicalCoupledMerge`, `open BinaryOpeningPayment (field field_computes field_encode)`, `open BinaryCoupled (stateBits outcomeBits outputBits)`):
--
--   ```lean
--   lemma run_initial_s238r (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
--       (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset (Fin m))
--       (v M l u : ℚ) (eta lo hi : ℝ) (N precision total k : ℕ)
--       (hF : F.Nonempty) (hM : 0<M) (hN : 3 ≤ N)
--       (hv : (0:ℝ)<v) (hv1 : (v:ℝ)<1/6) (hlo : 0<lo) (heta : 0 ≤ eta)
--       (hhi : hi ≤ 8*N*(M:ℝ)) (hprecision : (1/(2:ℚ)^precision:ℚ) ≤ eta)
--       (hdiam : ∀ i∈F,∀ j,dist i (loc j) ≤ (M:ℝ))
--       (T U : List (List (Label (Fin m)))) (hc : Certified loc F v eta lo hi 0 total k (initial l u T U)) :
--       run (pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) ∅ v 0 0)
--         (20*N*M) precision k ⟨0,total,.inr (initial l u T U)⟩)=
--         outputBits (CanonicalCoupledMerge.run loc distance F v M N precision k 0 total (initial l u T U))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.original` (definitions bundle `Q238L008` of this split); `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Output` and `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.State` (definitions bundle `Q238L019` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.outputBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.pack` and `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Frame` (definitions bundle `Q238L025` of this split); `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Certified`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.initial` and `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.run` (definitions bundle `Q238L026` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.pack` (definitions bundle `Q238L029` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.run` (definitions bundle `Q238L049` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.run_pack_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/InitialLoop.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.run_initial)

import Mathlib
import Definitions.Def_Q238L049

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledLoop
open WordOperations WordList BinaryArithmetic RationalLeaves RationalHeight CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryCoupled (stateBits outcomeBits outputBits)
variable {m d : ℕ} [PseudoMetricSpace (Fin m)]
attribute [local instance] RationalLeaves.metric
lemma run_initial_s238r (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset (Fin m))
    (v M l u : ℚ) (eta lo hi : ℝ) (N precision total k : ℕ)
    (hF : F.Nonempty) (hM : 0<M) (hN : 3 ≤ N)
    (hv : (0:ℝ)<v) (hv1 : (v:ℝ)<1/6) (hlo : 0<lo) (heta : 0 ≤ eta)
    (hhi : hi ≤ 8*N*(M:ℝ)) (hprecision : (1/(2:ℚ)^precision:ℚ) ≤ eta)
    (hdiam : ∀ i∈F,∀ j,dist i (loc j) ≤ (M:ℝ))
    (T U : List (List (Label (Fin m)))) (hc : Certified loc F v eta lo hi 0 total k (initial l u T U)) :
    run (pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) ∅ v 0 0)
      (20*N*M) precision k ⟨0,total,.inr (initial l u T U)⟩)=
      outputBits (CanonicalCoupledMerge.run loc distance F v M N precision k 0 total (initial l u T U)) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryCoupledLoop

end OAI
end
