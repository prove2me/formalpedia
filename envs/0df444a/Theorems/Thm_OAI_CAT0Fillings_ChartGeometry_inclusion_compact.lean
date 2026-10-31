-- Prove2me | Theorems.Thm_OAI_CAT0Fillings_ChartGeometry_inclusion_compact
-- name    : OAI.CAT0Fillings.ChartGeometry.inclusion_compact
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T02:46:01.402275+00:00
-- url     : https://prove2.me/theorems/68587aca-cf9a-48f2-88e5-6a22a2656ccb
-- title:
--   OAI.CAT0Fillings.ChartGeometry.inclusion_compact: intermediate lemma from OpenAI, Sharp integral fillings in CAT(0) spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CAT0Fillings.sharp_integral_filling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp integral fillings in CAT(0) spaces*, OpenAI Math Release, September 23, 2026, result family 337, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CAT0Fillings.ChartGeometry.inclusion_compact` of [lean/OAI/Geometry/CAT0Fillings/Sobolev/Compact.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/CAT0Fillings/Sobolev/Compact.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CAT0Fillings.ChartGeometry`, with `open Set Filter MeasureTheory Metric`, `open scoped Topology NNReal ENNReal`, `open Foundations`):
--
--   ```lean
--   theorem inclusion_compact
--       (h : Slicing.NormalApprox (k+1) T) (hz : boundarySucc T = 0) (hX : IsCAT0 X)
--       {p A B C : ℝ} (hp : 2 < p) (hA : 0 < A) (hB : 0 ≤ B) (hC : 0 ≤ C)
--       (hb : ∀ (u : X → ℝ) (K : ℝ≥0), LipschitzWith K u →
--         A*lpNorm u (ENNReal.ofReal p) (MassMeasure.currentMassMeasure hT)^2 ≤
--           B*(q.energyMeasure u).real univ+C*lpNorm u 2 (MassMeasure.currentMassMeasure hT)^2) :
--       IsCompactOperator q.inclusion
--   ```
--
--   **Definitions.** The statement is written with `OAI.CAT0Fillings.ChartGeometry`, `OAI.CAT0Fillings.ChartGeometry.GraphAmbient`, `OAI.CAT0Fillings.ChartGeometry.Sobolev`, `OAI.CAT0Fillings.ChartGeometry.atlasMeasure`, `OAI.CAT0Fillings.ChartGeometry.energyMeasure`, `OAI.CAT0Fillings.ChartGeometry.inclusion`, `OAI.CAT0Fillings.MassMeasure.currentMassMeasure` and `OAI.CAT0Fillings.Slicing.NormalApprox` (definitions bundle `OAIQ29C0000` of this split); `OAI.CAT0Fillings.Euc`, `OAI.CAT0Fillings.Functional`, `OAI.CAT0Fillings.IsCAT0`, `OAI.CAT0Fillings.IsMetricCurrent` and `OAI.CAT0Fillings.boundarySucc` (the published bundle `Def_SharpCAT0Filling`).
--
--   **Used by.** The proof of `OAI.CAT0Fillings.extremal_critical_minimizer` of this split imports it.
-- source:
--   OpenAI, Sharp integral fillings in CAT(0) spaces, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 337; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/CAT0Fillings/Sobolev/Compact.lean (declaration OAI.CAT0Fillings.ChartGeometry.inclusion_compact)

import Mathlib
import Definitions.Def_SharpCAT0Filling
import Definitions.Def_OAIQ29C0000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
open Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

theorem inclusion_compact
    (h : Slicing.NormalApprox (k+1) T) (hz : boundarySucc T = 0) (hX : IsCAT0 X)
    {p A B C : ℝ} (hp : 2 < p) (hA : 0 < A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ (u : X → ℝ) (K : ℝ≥0), LipschitzWith K u →
      A*lpNorm u (ENNReal.ofReal p) (MassMeasure.currentMassMeasure hT)^2 ≤
        B*(q.energyMeasure u).real univ+C*lpNorm u 2 (MassMeasure.currentMassMeasure hT)^2) :
    IsCompactOperator q.inclusion := by
  sorry

end CAT0Fillings.ChartGeometry
end

end OAI
end
