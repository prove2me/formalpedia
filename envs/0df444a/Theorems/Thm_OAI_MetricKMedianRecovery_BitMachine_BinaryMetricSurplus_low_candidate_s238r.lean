-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryMetricSurplus_low_candidate_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.low_candidate_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:17:11.40669+00:00
-- url     : https://prove2.me/theorems/003389b3-4e9b-490a-bae0-1f8d9b907e15
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.low_candidate_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.low_candidate` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralDispatchGuarantee.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralDispatchGuarantee.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus`, with `open LocalSearch Anchoring`):
--
--   ```lean
--   lemma low_candidate_s238r (δ : Fin n→ Fin n→ℕ) (F D : Finset (Fin n))
--       (k L M N C : ℕ) (v : ℚ) (hD : D.Nonempty) (hL : 0<L) (hk : 2*L<k) (hkF : k≤ F.card)
--       (hN : N=D.card+F.card) (hM : 0<M) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
--       (hfar : ∀ i∈F,∀ p∈D,1≤ dist i p) (hdiam : ∀ p∈D,∀ i∈F,δ p i≤ M)
--       (hcap : ∀ p∈D,∀ i∈F,δ p i≤ Rounding.cap D.card (IntegralAssembly.gamma/16))
--       (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)≤1/12)
--       (hvc : (v:ℝ)≤ strictnessGap (200*countConstant (1/100))/1000)
--       (hsmall : (v:ℝ)^2≤ strictnessGap (200*countConstant (1/100))/(6*(200*countConstant (1/100)+2)))
--       (hsize : 2/(N:ℝ)≤ strictnessGap (200*countConstant (1/100))/200)
--       (herror : (N:ℝ)^2/2^N≤(v:ℝ))
--       (hfree : 3*(HistoryPhaseBound.limit v ((M:ℝ)+8*(D.card:ℝ)*(M:ℝ))+1)≤ L)
--       (hC : 2≤(1+v^2)^C) :
--       ∃ S : Finset (Fin n),run v C (pack (fun i j=>(δ i j:ℚ)) D F M (k-L) L)=BinaryFinSet.encode S ∧
--         S⊆F ∧ S.Nonempty ∧ S.card=k ∧ WidthLocalMin F D S 5 ∧
--         ∀ xi : ℝ,0≤ xi→ xi≤1→ optimum F D (k-2*L)≤(1+xi)*optimum F D k→
--           cost D S≤(2-IntegralAssembly.gamma)*(1+xi)*optimum F D k
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Anchoring.countConstant` (definitions bundle `Q238L000` of this split); `OAI.MetricKMedianRecovery.strictnessGap` and `OAI.MetricKMedianRecovery.Rounding.cap` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.HistoryPhaseBound.limit` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.IntegralAssembly.gamma` (definitions bundle `Q238L009` of this split); `OAI.MetricKMedianRecovery.LocalSearch.WidthLocalMin`, `OAI.MetricKMedianRecovery.LocalSearch.cost` and `OAI.MetricKMedianRecovery.LocalSearch.optimum` (definitions bundle `Q238L010` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238L017` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.pack` (definitions bundle `Q238L030` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.run` (definitions bundle `Q238L052` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.finite_program_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralDispatchGuarantee.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.low_candidate)

import Mathlib
import Definitions.Def_Q238L052

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricSurplus
open LocalSearch Anchoring
variable {n : ℕ} [MetricSpace (Fin n)]
attribute [local irreducible] run BinaryCanonicalSurplus.run
lemma low_candidate_s238r (δ : Fin n→ Fin n→ℕ) (F D : Finset (Fin n))
    (k L M N C : ℕ) (v : ℚ) (hD : D.Nonempty) (hL : 0<L) (hk : 2*L<k) (hkF : k≤ F.card)
    (hN : N=D.card+F.card) (hM : 0<M) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (hfar : ∀ i∈F,∀ p∈D,1≤ dist i p) (hdiam : ∀ p∈D,∀ i∈F,δ p i≤ M)
    (hcap : ∀ p∈D,∀ i∈F,δ p i≤ Rounding.cap D.card (IntegralAssembly.gamma/16))
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)≤1/12)
    (hvc : (v:ℝ)≤ strictnessGap (200*countConstant (1/100))/1000)
    (hsmall : (v:ℝ)^2≤ strictnessGap (200*countConstant (1/100))/(6*(200*countConstant (1/100)+2)))
    (hsize : 2/(N:ℝ)≤ strictnessGap (200*countConstant (1/100))/200)
    (herror : (N:ℝ)^2/2^N≤(v:ℝ))
    (hfree : 3*(HistoryPhaseBound.limit v ((M:ℝ)+8*(D.card:ℝ)*(M:ℝ))+1)≤ L)
    (hC : 2≤(1+v^2)^C) :
    ∃ S : Finset (Fin n),run v C (pack (fun i j=>(δ i j:ℚ)) D F M (k-L) L)=BinaryFinSet.encode S ∧
      S⊆F ∧ S.Nonempty ∧ S.card=k ∧ WidthLocalMin F D S 5 ∧
      ∀ xi : ℝ,0≤ xi→ xi≤1→ optimum F D (k-2*L)≤(1+xi)*optimum F D k→
        cost D S≤(2-IntegralAssembly.gamma)*(1+xi)*optimum F D k := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryMetricSurplus

end OAI
end
