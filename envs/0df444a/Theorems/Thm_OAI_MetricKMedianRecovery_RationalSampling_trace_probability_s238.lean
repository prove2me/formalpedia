-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_RationalSampling_trace_probability_s238
-- name    : OAI.MetricKMedianRecovery.RationalSampling.trace_probability_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:32:49.913559+00:00
-- url     : https://prove2.me/theorems/383ba918-7a32-449e-af66-4eaeb86fbf63
-- title:
--   OAI.MetricKMedianRecovery.RationalSampling.trace_probability_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.RationalSampling.trace_probability` of [lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplerLaw.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplerLaw.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.RationalSampling`, with `open Sampling BitMachine Guided FiniteSampling`):
--
--   ```lean
--   lemma trace_probability_s238 (D F S : Finset (Fin n)) (hD : D.Nonempty) (Δ P κ : ℚ) (m M E J b t : ℕ)
--       (hM : 0<M) (hJ : 0<J) (s : Option (State n)) (G : (Fin (t+1)→Option (Sampling.State (Fin n)))→Prop) :
--       probability (fun seed : Fin t→Fin b→Bool=>G (fun i=>(((List.ofFn seed).take i.val).foldl
--         (next δ D F S Δ P κ m M E J b) s).map State.real))=
--         probability (fun seed=>G (states (Sampling.update D F S hD (Δ:ℝ) (P:ℝ) (κ:ℝ) m M E J) t (s.map State.real)
--           (FixedDyadic.actions (Sampling.update D F S hD (Δ:ℝ) (P:ℝ) (κ:ℝ) m M E J)
--             (actualKernel D S (Δ:ℝ) M E J hM hJ) b (Sum.inl ()) t (s.map State.real) seed)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.FiniteSampling.probability`, `OAI.MetricKMedianRecovery.RationalSampling.State`, `OAI.MetricKMedianRecovery.Sampling.State` and `OAI.MetricKMedianRecovery.RationalSampling.State.real` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.Sampling.Action` and `OAI.MetricKMedianRecovery.Sampling.Entry` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.Guided.states` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.Guided.FixedDyadic.actions` (definitions bundle `Q238K015` of this split); `OAI.MetricKMedianRecovery.RationalSampling.next` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.Sampling.actualKernel` and `OAI.MetricKMedianRecovery.Sampling.update` (definitions bundle `Q238K022` of this split).
--
--   **Used by.** The proofs of `OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Fair_output_exponential_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.output_success_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplerLaw.lean (declaration OAI.MetricKMedianRecovery.RationalSampling.trace_probability)

import Mathlib
import Definitions.Def_Q238K021
import Definitions.Def_Q238K022

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open Sampling BitMachine Guided FiniteSampling
variable {n : ℕ} [PseudoMetricSpace (Fin n)] (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
include hδ
lemma trace_probability_s238 (D F S : Finset (Fin n)) (hD : D.Nonempty) (Δ P κ : ℚ) (m M E J b t : ℕ)
    (hM : 0<M) (hJ : 0<J) (s : Option (State n)) (G : (Fin (t+1)→Option (Sampling.State (Fin n)))→Prop) :
    probability (fun seed : Fin t→Fin b→Bool=>G (fun i=>(((List.ofFn seed).take i.val).foldl
      (next δ D F S Δ P κ m M E J b) s).map State.real))=
      probability (fun seed=>G (states (Sampling.update D F S hD (Δ:ℝ) (P:ℝ) (κ:ℝ) m M E J) t (s.map State.real)
        (FixedDyadic.actions (Sampling.update D F S hD (Δ:ℝ) (P:ℝ) (κ:ℝ) m M E J)
          (actualKernel D S (Δ:ℝ) M E J hM hJ) b (Sum.inl ()) t (s.map State.real) seed))) := by
  sorry
end MetricKMedianRecovery.RationalSampling

end OAI
end
