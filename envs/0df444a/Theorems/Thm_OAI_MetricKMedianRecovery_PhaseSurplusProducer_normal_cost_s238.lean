-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_PhaseSurplusProducer_normal_cost_s238
-- name    : OAI.MetricKMedianRecovery.PhaseSurplusProducer.normal_cost_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:24:46.268869+00:00
-- url     : https://prove2.me/theorems/29e19317-b5d7-4a38-b576-98e6f51f6a34
-- title:
--   OAI.MetricKMedianRecovery.PhaseSurplusProducer.normal_cost_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.PhaseSurplusProducer.normal_cost` of [lean/OAI/Combinatorics/KMedianRecovery/Geometry/IndexedCost.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/IndexedCost.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.PhaseSurplusProducer`, with `open PhaseOriginalLedger LocalSearch Anchoring`):
--
--   ```lean
--   lemma normal_cost_s238 (F D O S H : Finset V) (hO : O.Nonempty) (hS : S.Nonempty)
--       (hH : H.Nonempty) (hOF : O ⊆ F) (hSF : S ⊆ F) (hHF : H ⊆ F)
--       (hO2 : 2 ≤ O.card) (L : ℕ) (hcard : S.card = O.card+L) (hHL : H.card+L = O.card)
--       (hlocal : WidthLocalMin F D S 5) (hP : 0 < cost D O)
--       (alpha : D → ℝ) (lam Q eta xi v : ℝ) (hdual : Dual (fun j : D => j.val) F v lam alpha)
--       (hlam : 0 < lam) (hQ : 0 ≤ Q) (hSQ : cost D S ≤ Q)
--       (hHcost : cost D H ≤ (1+xi)*cost D O) (hxi : xi ≤ 1)
--       (hv : 0 < v) (hv1 : v ≤ 1/12)
--       (hvc : v ≤ strictnessGap (200*countConstant (1/100))/1000)
--       (hsmall : v^2 ≤ strictnessGap (200*countConstant (1/100))/(6*(200*countConstant (1/100)+2)))
--       (herr : (O.card:ℝ)*D.card*eta ≤ v*cost D O)
--       (hpayment : (1-3*v)*Q+(O.card:ℝ)*(lam-(D.card:ℝ)*eta) ≤ ∑ j, alpha j) :
--       cost D S ≤ (2-strictnessGap (200*countConstant (1/100))/100)*cost D O
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Anchoring.countConstant` (definitions bundle `Q238K000` of this split); `OAI.MetricKMedianRecovery.strictnessGap` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.PhaseOriginalLedger.Dual` (definitions bundle `Q238K014` of this split); `OAI.MetricKMedianRecovery.LocalSearch.WidthLocalMin` and `OAI.MetricKMedianRecovery.LocalSearch.cost` (definitions bundle `Q238K015` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus.produce_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/IndexedCost.lean (declaration OAI.MetricKMedianRecovery.PhaseSurplusProducer.normal_cost)

import Mathlib
import Definitions.Def_Q238K014
import Definitions.Def_Q238K015

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseSurplusProducer
open PhaseOriginalLedger LocalSearch Anchoring
variable {V : Type*} [MetricSpace V] [DecidableEq V]

variable [Fintype V]

lemma normal_cost_s238 (F D O S H : Finset V) (hO : O.Nonempty) (hS : S.Nonempty)
    (hH : H.Nonempty) (hOF : O ⊆ F) (hSF : S ⊆ F) (hHF : H ⊆ F)
    (hO2 : 2 ≤ O.card) (L : ℕ) (hcard : S.card = O.card+L) (hHL : H.card+L = O.card)
    (hlocal : WidthLocalMin F D S 5) (hP : 0 < cost D O)
    (alpha : D → ℝ) (lam Q eta xi v : ℝ) (hdual : Dual (fun j : D => j.val) F v lam alpha)
    (hlam : 0 < lam) (hQ : 0 ≤ Q) (hSQ : cost D S ≤ Q)
    (hHcost : cost D H ≤ (1+xi)*cost D O) (hxi : xi ≤ 1)
    (hv : 0 < v) (hv1 : v ≤ 1/12)
    (hvc : v ≤ strictnessGap (200*countConstant (1/100))/1000)
    (hsmall : v^2 ≤ strictnessGap (200*countConstant (1/100))/(6*(200*countConstant (1/100)+2)))
    (herr : (O.card:ℝ)*D.card*eta ≤ v*cost D O)
    (hpayment : (1-3*v)*Q+(O.card:ℝ)*(lam-(D.card:ℝ)*eta) ≤ ∑ j, alpha j) :
    cost D S ≤ (2-strictnessGap (200*countConstant (1/100))/100)*cost D O := by
  sorry

end MetricKMedianRecovery.PhaseSurplusProducer

end OAI
end
