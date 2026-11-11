-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCanonicalSurplus_produce_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus.produce_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:15:12.869197+00:00
-- url     : https://prove2.me/theorems/9e7b1cc1-1955-4f66-82d6-2a2f5f0e75fe
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus.produce_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus.produce` of [lean/OAI/Combinatorics/KMedianRecovery/Strictness/SurplusPostprocess.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Strictness/SurplusPostprocess.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus`, with `open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma produce_s238 [MetricSpace (Fin m)] (δ : Fin m→Fin m→ℕ) (F D : Finset (Fin m))
--       (h L M N C : ℕ) (v : ℚ) (hD : D.Nonempty) (hh : 2≤h) (hkF : h+L≤F.card)
--       (hN : N=D.card+F.card) (hM : 0<M)
--       (hδ : ∀ p∈D,∀ i∈F,(δ p i:ℝ)=dist p i)
--       (hmetric : ∀ i j,(δ (SortedIndex.enum D j) i:ℝ)=dist i (SortedIndex.enum D j))
--       (hfar : ∀ i∈F,∀ p∈D,1≤dist i p)
--       (hdiam : ∀ p∈D,∀ i∈F,δ p i≤M)
--       (hcap : ∀ p∈D,∀ i∈F,δ p i≤Rounding.cap D.card (IntegralAssembly.gamma/16))
--       (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)≤1/12)
--       (hvc : (v:ℝ)≤ strictnessGap (200*Anchoring.countConstant (1/100))/1000)
--       (hsmall : (v:ℝ)^2≤ strictnessGap (200*Anchoring.countConstant (1/100))/(6*(200*Anchoring.countConstant (1/100)+2)))
--       (hsize : 2/(N:ℝ)≤ strictnessGap (200*Anchoring.countConstant (1/100))/200)
--       (herror : (N:ℝ)^2/2^N≤(v:ℝ))
--       (hL : 3*(HistoryPhaseBound.limit v ((M:ℝ)+8*(D.card:ℝ)*(M:ℝ))+1)≤L)
--       (hC : 2≤(1+v^2)^C) :
--       ∃ S : Finset (Fin m),run v C (pack δ F D M h L)=BinaryFinSet.encode S ∧
--         S⊆F ∧ S.Nonempty ∧ S.card=h+L ∧ LocalSearch.WidthLocalMin F D S 5 ∧
--         ∀ O H : Finset (Fin m),∀ xi : ℝ,
--           O⊆F→O.card=h→H⊆F→H.Nonempty→H.card+L=h→
--           LocalSearch.cost D H≤(1+xi)*LocalSearch.cost D O→xi≤1→
--           LocalSearch.cost D S≤(2-strictnessGap (200*Anchoring.countConstant (1/100))/100)*LocalSearch.cost D O
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Anchoring.countConstant` (definitions bundle `Q238K000` of this split); `OAI.MetricKMedianRecovery.SortedIndex.enum` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.strictnessGap` and `OAI.MetricKMedianRecovery.Rounding.cap` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.HistoryPhaseBound.limit` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238K010` of this split); `OAI.MetricKMedianRecovery.IntegralAssembly.gamma` (definitions bundle `Q238K013` of this split); `OAI.MetricKMedianRecovery.LocalSearch.WidthLocalMin` and `OAI.MetricKMedianRecovery.LocalSearch.cost` (definitions bundle `Q238K015` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus.pack` (definitions bundle `Q238K020` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus.run` (definitions bundle `Q238K049` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.low_candidate_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Strictness/SurplusPostprocess.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus.produce)

import Mathlib
import Definitions.Def_Q238K049

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
variable {m : ℕ}
lemma produce_s238 [MetricSpace (Fin m)] (δ : Fin m→Fin m→ℕ) (F D : Finset (Fin m))
    (h L M N C : ℕ) (v : ℚ) (hD : D.Nonempty) (hh : 2≤h) (hkF : h+L≤F.card)
    (hN : N=D.card+F.card) (hM : 0<M)
    (hδ : ∀ p∈D,∀ i∈F,(δ p i:ℝ)=dist p i)
    (hmetric : ∀ i j,(δ (SortedIndex.enum D j) i:ℝ)=dist i (SortedIndex.enum D j))
    (hfar : ∀ i∈F,∀ p∈D,1≤dist i p)
    (hdiam : ∀ p∈D,∀ i∈F,δ p i≤M)
    (hcap : ∀ p∈D,∀ i∈F,δ p i≤Rounding.cap D.card (IntegralAssembly.gamma/16))
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)≤1/12)
    (hvc : (v:ℝ)≤ strictnessGap (200*Anchoring.countConstant (1/100))/1000)
    (hsmall : (v:ℝ)^2≤ strictnessGap (200*Anchoring.countConstant (1/100))/(6*(200*Anchoring.countConstant (1/100)+2)))
    (hsize : 2/(N:ℝ)≤ strictnessGap (200*Anchoring.countConstant (1/100))/200)
    (herror : (N:ℝ)^2/2^N≤(v:ℝ))
    (hL : 3*(HistoryPhaseBound.limit v ((M:ℝ)+8*(D.card:ℝ)*(M:ℝ))+1)≤L)
    (hC : 2≤(1+v^2)^C) :
    ∃ S : Finset (Fin m),run v C (pack δ F D M h L)=BinaryFinSet.encode S ∧
      S⊆F ∧ S.Nonempty ∧ S.card=h+L ∧ LocalSearch.WidthLocalMin F D S 5 ∧
      ∀ O H : Finset (Fin m),∀ xi : ℝ,
        O⊆F→O.card=h→H⊆F→H.Nonempty→H.card+L=h→
        LocalSearch.cost D H≤(1+xi)*LocalSearch.cost D O→xi≤1→
        LocalSearch.cost D S≤(2-strictnessGap (200*Anchoring.countConstant (1/100))/100)*LocalSearch.cost D O := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus

end OAI
end
