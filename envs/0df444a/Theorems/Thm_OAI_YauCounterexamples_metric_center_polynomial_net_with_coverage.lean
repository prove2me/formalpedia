-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_metric_center_polynomial_net_with_coverage
-- name    : OAI.YauCounterexamples.metric_center_polynomial_net_with_coverage
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:44:15.714611+00:00
-- url     : https://prove2.me/theorems/e0739dd1-dac2-4224-9733-93af78d10785
-- title:
--   OAI.YauCounterexamples.metric_center_polynomial_net_with_coverage: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.metric_center_polynomial_net_with_coverage` of [lean/OAI/Geometry/SmoothYau/Geometry/MetricCenterPolynomialNetCoverage.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/MetricCenterPolynomialNetCoverage.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set`, `open scoped Topology ContDiff`):
--
--   ```lean
--   theorem metric_center_polynomial_net_with_coverage
--       (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
--       {K : Set NormalWaveSpace} (hK : IsCompact K) (r₀ : ℝ) (hr₀ : 0 < r₀) :
--       ∃ Q > 0, ∀ n : ℝ, 1 ≤ n →
--         ∃ t : Finset (Fin 3 → ℝ), ∃ p : t → metricFrameSet g K,
--           (t.card : ℝ) ≤ Q*n^3 ∧
--           ∀ y ∈ normalWaveEquiv.symm '' K, ∃ i : t, ∃ x : Fin 3 → ℝ,
--             ‖x‖ < r₀ ∧ ‖x‖ ≤ 1/n ∧ normalCoordinateMap g (p i) x = y ∧
--             n*‖normalWaveEquiv y-(p i).1.1‖ ≤ 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.NormalWaveSpace` and `OAI.YauCounterexamples.normalWaveEquiv` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.metricFrameSet` and `OAI.YauCounterexamples.normalCoordinateMap` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.SmoothMetric` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proofs of `OAI_YauCounterexamples_compact_actual_metric_packets_supported` and `OAI.YauCounterexamples.compact_actual_waves_sign_and_jets_supported` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Geometry/MetricCenterPolynomialNetCoverage.lean (declaration OAI.YauCounterexamples.metric_center_polynomial_net_with_coverage)

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A007

section

attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.coordinateRegionMeasure_finite _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set
open scoped Topology ContDiff
theorem metric_center_polynomial_net_with_coverage
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) (r₀ : ℝ) (hr₀ : 0 < r₀) :
    ∃ Q > 0, ∀ n : ℝ, 1 ≤ n →
      ∃ t : Finset (Fin 3 → ℝ), ∃ p : t → metricFrameSet g K,
        (t.card : ℝ) ≤ Q*n^3 ∧
        ∀ y ∈ normalWaveEquiv.symm '' K, ∃ i : t, ∃ x : Fin 3 → ℝ,
          ‖x‖ < r₀ ∧ ‖x‖ ≤ 1/n ∧ normalCoordinateMap g (p i) x = y ∧
          n*‖normalWaveEquiv y-(p i).1.1‖ ≤ 1 := by
  sorry

end YauCounterexamples
end

end OAI
end
