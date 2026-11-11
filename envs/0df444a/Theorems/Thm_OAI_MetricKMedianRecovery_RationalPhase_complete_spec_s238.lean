-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_RationalPhase_complete_spec_s238
-- name    : OAI.MetricKMedianRecovery.RationalPhase.complete_spec_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:30:51.007201+00:00
-- url     : https://prove2.me/theorems/00123ed4-f553-436a-8345-d061a0b66097
-- title:
--   OAI.MetricKMedianRecovery.RationalPhase.complete_spec_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.RationalPhase.complete_spec` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/FinishSpec.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/FinishSpec.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.RationalPhase`, with `open EffectiveOpenability OrdinaryProducer`):
--
--   ```lean
--   theorem complete_spec_s238 {m d : ℕ} [PseudoMetricSpace (Fin m)]
--       (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
--       (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
--       (F : Finset (Fin m)) (v lam : ℚ)
--       (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6)
--       (s : State m d) (hz : (0:ℝ)≤(s.phase:ℝ)) :
--       let r := finish distance F v lam F.card s
--       CountedTrace (PlainOpening loc F (v:ℝ) (lam:ℝ)) r.2.length s.real r.1.real ∧
--       r.2.length≤F.card ∧ (F\r.1.opened).card+r.2.length=(F\s.opened).card ∧
--       s.opened ⊆ r.1.opened ∧ r.1.opened ⊆ s.opened∪F ∧
--       r.1.phase=s.phase ∧ PhaseMaximal loc F (v:ℝ) (lam:ℝ) r.1.real
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.ExecutionState` (definitions bundle `Q238K000` of this split); `OAI.MetricKMedianRecovery.RationalPhase.State` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.CountedTrace` and `OAI.MetricKMedianRecovery.RationalPhase.Event` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.OrdinaryProducer.PhaseMaximal`, `OAI.MetricKMedianRecovery.OrdinaryProducer.PlainOpening` and `OAI.MetricKMedianRecovery.RationalPhase.State.real` (definitions bundle `Q238K015` of this split); `OAI.MetricKMedianRecovery.RationalPhase.finish` (definitions bundle `Q238K022` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.continuation_spec_s238` and `OAI.MetricKMedianRecovery.RationalPhase.completion_spec_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/FinishSpec.lean (declaration OAI.MetricKMedianRecovery.RationalPhase.complete_spec)

import Mathlib
import Definitions.Def_Q238K022

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalPhase
open EffectiveOpenability OrdinaryProducer

theorem complete_spec_s238 {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (F : Finset (Fin m)) (v lam : ℚ)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6)
    (s : State m d) (hz : (0:ℝ)≤(s.phase:ℝ)) :
    let r := finish distance F v lam F.card s
    CountedTrace (PlainOpening loc F (v:ℝ) (lam:ℝ)) r.2.length s.real r.1.real ∧
    r.2.length≤F.card ∧ (F\r.1.opened).card+r.2.length=(F\s.opened).card ∧
    s.opened ⊆ r.1.opened ∧ r.1.opened ⊆ s.opened∪F ∧
    r.1.phase=s.phase ∧ PhaseMaximal loc F (v:ℝ) (lam:ℝ) r.1.real := by
  sorry

end MetricKMedianRecovery.RationalPhase

end OAI
end
