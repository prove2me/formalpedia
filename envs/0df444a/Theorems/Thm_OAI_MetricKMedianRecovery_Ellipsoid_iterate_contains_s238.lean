-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_iterate_contains_s238
-- name    : OAI.MetricKMedianRecovery.Ellipsoid.iterate_contains_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:20:52.714358+00:00
-- url     : https://prove2.me/theorems/12d5c38f-9416-4116-884d-70365e8c44e7
-- title:
--   OAI.MetricKMedianRecovery.Ellipsoid.iterate_contains_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.Ellipsoid.iterate_contains` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/State.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/State.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.Ellipsoid`, with `open Matrix RationalLinearFeasibility`, `open scoped Matrix`):
--
--   ```lean
--   lemma iterate_contains_s238 {n : ℕ} (D : ℕ) (hD : 0<D) (rows : List (Row n)) (S : State n)
--       (hn : 2≤n) (hS : (realMatrix S.shape).PosDef) (x : Fin n → ℝ)
--       (hx : ∀ q∈rows, q.RealHolds x)
--       (hball : quad (realMatrix S.shape)⁻¹ (x-realVector S.center)≤1) (t : ℕ) :
--       quad (realMatrix (iterate D rows S t).shape)⁻¹ (x-realVector (iterate D rows S t).center)≤1
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLinearFeasibility.Row` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.Ellipsoid.State` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.Ellipsoid.quad`, `OAI.MetricKMedianRecovery.Ellipsoid.realMatrix` and `OAI.MetricKMedianRecovery.Ellipsoid.realVector` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.Ellipsoid.iterate` (definitions bundle `Q238K014` of this split); `OAI.MetricKMedianRecovery.RationalLinearFeasibility.Row.RealHolds` (definitions bundle `Q238K015` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.Ellipsoid.weakSolve_complete_diameters_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/State.lean (declaration OAI.MetricKMedianRecovery.Ellipsoid.iterate_contains)

import Mathlib
import Definitions.Def_Q238K014
import Definitions.Def_Q238K015

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility
open scoped Matrix

lemma iterate_contains_s238 {n : ℕ} (D : ℕ) (hD : 0<D) (rows : List (Row n)) (S : State n)
    (hn : 2≤n) (hS : (realMatrix S.shape).PosDef) (x : Fin n → ℝ)
    (hx : ∀ q∈rows, q.RealHolds x)
    (hball : quad (realMatrix S.shape)⁻¹ (x-realVector S.center)≤1) (t : ℕ) :
    quad (realMatrix (iterate D rows S t).shape)⁻¹ (x-realVector (iterate D rows S t).center)≤1 := by
  sorry

end MetricKMedianRecovery.Ellipsoid

end OAI
end
