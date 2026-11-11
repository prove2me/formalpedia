-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryInitialProject_run_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.run_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:11:51.978611+00:00
-- url     : https://prove2.me/theorems/e1f7431e-93ea-41bb-a51d-1dbcd10e899a
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.run_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.run_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/InitialProject.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/InitialProject.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject`, with `open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge`, `open BinaryOpeningPayment (field field_computes field_encode)`, `open BinaryFiniteContext (labels setBits)`):
--
--   ```lean
--   lemma run_pack_s238 [PseudoMetricSpace (Fin m)] (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
--       (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset (Fin m))
--       (v M : ℚ) (C k : ℕ) (hv : 0<v) (hC : 2≤(1+v^2)^C)
--       (hd : 0<d) (hk : 2≤k) (hF : F.Nonempty) (hM : 0<M) (hN : 3≤d+F.card)
--       (hv1 : (v:ℝ)<1/6) (hlohi : 2/((d+F.card:ℕ):ℚ)^2≤8*(d:ℚ)*M)
--       (hfar : ∀ i∈F,∀ j,1≤dist i (loc j)) (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤(M:ℝ)) :
--       run v C (BinaryInitialAuto.pack distance loc F M k)=BinaryFinSet.encode
--         (start loc distance F v (2/((d+F.card:ℕ):ℚ)^2) M (d+F.card) (d+F.card)
--           (HistoryPhaseBound.limit v ((M:ℝ)+8*(d:ℝ)*M)+1) k).project
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.HistoryPhaseBound.limit` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238K010` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialAuto.pack` (definitions bundle `Q238K020` of this split); `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.StartOutput.project` (definitions bundle `Q238K027` of this split); `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start` (definitions bundle `Q238K031` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.run` (definitions bundle `Q238K043` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus.produce_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/InitialProject.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.run_pack)

import Mathlib
import Definitions.Def_Q238K043

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInitialProject
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
variable {m d : ℕ}
attribute [local irreducible] BinaryProjection.run BinaryFiniteMachine.after
lemma run_pack_s238 [PseudoMetricSpace (Fin m)] (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset (Fin m))
    (v M : ℚ) (C k : ℕ) (hv : 0<v) (hC : 2≤(1+v^2)^C)
    (hd : 0<d) (hk : 2≤k) (hF : F.Nonempty) (hM : 0<M) (hN : 3≤d+F.card)
    (hv1 : (v:ℝ)<1/6) (hlohi : 2/((d+F.card:ℕ):ℚ)^2≤8*(d:ℚ)*M)
    (hfar : ∀ i∈F,∀ j,1≤dist i (loc j)) (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤(M:ℝ)) :
    run v C (BinaryInitialAuto.pack distance loc F M k)=BinaryFinSet.encode
      (start loc distance F v (2/((d+F.card:ℕ):ℚ)^2) M (d+F.card) (d+F.card)
        (HistoryPhaseBound.limit v ((M:ℝ)+8*(d:ℝ)*M)+1) k).project := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryInitialProject

end OAI
end
