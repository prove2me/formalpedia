-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_upperRound_inverse_bounds_s238r
-- name    : OAI.MetricKMedianRecovery.Ellipsoid.upperRound_inverse_bounds_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:23:11.168829+00:00
-- url     : https://prove2.me/theorems/ad57d572-ca43-4e91-9385-c407be602629
-- title:
--   OAI.MetricKMedianRecovery.Ellipsoid.upperRound_inverse_bounds_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.Ellipsoid.upperRound_inverse_bounds` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/CenterUpdate.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/CenterUpdate.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.Ellipsoid`, with `open Matrix`, `open scoped Matrix`):
--
--   ```lean
--   lemma upperRound_inverse_bounds_s238r (A Q : Matrix V V ℝ) (hA : A.PosDef) (hQ : Q.IsHermitian)
--       (e m ε : ℝ) (he : 0≤e) (hε : 0≤ε) (hε1 : ε<1)
--       (hentry : ∀ i j, |Q i j-A i j|≤e)
--       (hm : (A-m • (1:Matrix V V ℝ)).PosSemidef)
--       (hprecision : 2*(Fintype.card V:ℝ)*e≤ε*m) :
--       (A⁻¹-(upperRound Q e)⁻¹).PosSemidef ∧
--       ((upperRound Q e)⁻¹-(1-ε) • A⁻¹).PosSemidef
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Ellipsoid.upperRound` (definitions bundle `Q238L004` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.Ellipsoid.stepShape_pos_bounds_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/CenterUpdate.lean (declaration OAI.MetricKMedianRecovery.Ellipsoid.upperRound_inverse_bounds)

import Mathlib
import Definitions.Def_Q238L004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma upperRound_inverse_bounds_s238r (A Q : Matrix V V ℝ) (hA : A.PosDef) (hQ : Q.IsHermitian)
    (e m ε : ℝ) (he : 0≤e) (hε : 0≤ε) (hε1 : ε<1)
    (hentry : ∀ i j, |Q i j-A i j|≤e)
    (hm : (A-m • (1:Matrix V V ℝ)).PosSemidef)
    (hprecision : 2*(Fintype.card V:ℝ)*e≤ε*m) :
    (A⁻¹-(upperRound Q e)⁻¹).PosSemidef ∧
    ((upperRound Q e)⁻¹-(1-ε) • A⁻¹).PosSemidef := by
  sorry

end MetricKMedianRecovery.Ellipsoid

end OAI
end
