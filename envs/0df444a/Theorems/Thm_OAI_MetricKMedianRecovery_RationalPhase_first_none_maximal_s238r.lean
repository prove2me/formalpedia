-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_RationalPhase_first_none_maximal_s238r
-- name    : OAI.MetricKMedianRecovery.RationalPhase.first_none_maximal_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:35:58.167201+00:00
-- url     : https://prove2.me/theorems/727f43c8-31ee-45f2-8cf6-75b026be0e59
-- title:
--   OAI.MetricKMedianRecovery.RationalPhase.first_none_maximal_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.RationalPhase.first_none_maximal` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/StoredForms.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/StoredForms.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.RationalPhase`, with `open EffectiveOpenability OrdinaryProducer OpenabilityLinearization`):
--
--   ```lean
--   lemma first_none_maximal_s238r {m d : ℕ} [PseudoMetricSpace (Fin m)]
--       (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
--       (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
--       (F : Finset (Fin m)) (v lam : ℚ) (s : State m d)
--       (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hz : (0:ℝ)≤(s.phase:ℝ))
--       (he : first distance F s.opened v s.phase lam (List.ofFn (fun i : Fin m => i))=none) :
--       PhaseMaximal loc F (v:ℝ) (lam:ℝ) s.real
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalPhase.State` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.RationalPhase.Event` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.OrdinaryProducer.PhaseMaximal` (definitions bundle `Q238L010` of this split); `OAI.MetricKMedianRecovery.RationalPhase.State.real` (definitions bundle `Q238L011` of this split); `OAI.MetricKMedianRecovery.RationalPhase.first` (definitions bundle `Q238L020` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.RationalPhase.complete_spec_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/StoredForms.lean (declaration OAI.MetricKMedianRecovery.RationalPhase.first_none_maximal)

import Mathlib
import Definitions.Def_Q238L020

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalPhase
open EffectiveOpenability OrdinaryProducer OpenabilityLinearization

lemma first_none_maximal_s238r {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (F : Finset (Fin m)) (v lam : ℚ) (s : State m d)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hz : (0:ℝ)≤(s.phase:ℝ))
    (he : first distance F s.opened v s.phase lam (List.ofFn (fun i : Fin m => i))=none) :
    PhaseMaximal loc F (v:ℝ) (lam:ℝ) s.real := by
  sorry

end MetricKMedianRecovery.RationalPhase

end OAI
end
