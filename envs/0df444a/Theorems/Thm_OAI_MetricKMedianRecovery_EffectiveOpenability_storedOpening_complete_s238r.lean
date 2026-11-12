-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_EffectiveOpenability_storedOpening_complete_s238r
-- name    : OAI.MetricKMedianRecovery.EffectiveOpenability.storedOpening_complete_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:34:53.427635+00:00
-- url     : https://prove2.me/theorems/85dad4a4-af97-499a-9c74-225ac2f97d31
-- title:
--   OAI.MetricKMedianRecovery.EffectiveOpenability.storedOpening_complete_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.EffectiveOpenability.storedOpening_complete` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/StoredForms.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/StoredForms.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.EffectiveOpenability`, with `open RationalLinearFeasibility RationalOpenability OpenabilityLinearization`):
--
--   ```lean
--   lemma storedOpening_complete_s238r {m d : ℕ} [PseudoMetricSpace (Fin m)]
--       (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
--       (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
--       (F W : Finset (Fin m)) (v z lam eta : ℚ) (i : Fin m)
--       (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hz : (0:ℝ)≤(z:ℝ))
--       (h : etaOpenable loc F W (1-3*(v:ℝ)) (1+(v:ℝ)^2) (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i) :
--       ∃ x,storedOpening distance F W v z lam eta i=some x
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.etaOpenable` (definitions bundle `Q238L000` of this split); `OAI.MetricKMedianRecovery.RationalOpenability.Variables` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.EffectiveOpenability.storedOpening` (definitions bundle `Q238L020` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.RationalPhase.first_none_maximal_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/StoredForms.lean (declaration OAI.MetricKMedianRecovery.EffectiveOpenability.storedOpening_complete)

import Mathlib
import Definitions.Def_Q238L020

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.EffectiveOpenability
open RationalLinearFeasibility RationalOpenability OpenabilityLinearization

lemma storedOpening_complete_s238r {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (F W : Finset (Fin m)) (v z lam eta : ℚ) (i : Fin m)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hz : (0:ℝ)≤(z:ℝ))
    (h : etaOpenable loc F W (1-3*(v:ℝ)) (1+(v:ℝ)^2) (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i) :
    ∃ x,storedOpening distance F W v z lam eta i=some x := by
  sorry

end MetricKMedianRecovery.EffectiveOpenability

end OAI
end
