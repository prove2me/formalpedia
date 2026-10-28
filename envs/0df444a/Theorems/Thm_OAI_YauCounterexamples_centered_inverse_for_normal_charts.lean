-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_centered_inverse_for_normal_charts
-- name    : OAI.YauCounterexamples.centered_inverse_for_normal_charts
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:37:38.93181+00:00
-- url     : https://prove2.me/theorems/76c5ec21-c369-407e-8dc4-04f3889a1ca3
-- title:
--   OAI.YauCounterexamples.centered_inverse_for_normal_charts: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.centered_inverse_for_normal_charts` of [lean/OAI/Geometry/SmoothYau/Smoothness/CenteredNormalInverseFderiv.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/CenteredNormalInverseFderiv.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter`, `open scoped Topology ContDiff`):
--
--   ```lean
--   theorem centered_inverse_for_normal_charts
--       (g : SmoothMetric NormalWaveSpace NormalWaveSpace) {K : Set NormalWaveSpace} (hK : IsCompact K)
--       (e : NormalWaveParameter → OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace)
--       (he : ∀ q, (e q : NormalWaveSpace → NormalWaveSpace) = normalJetMap q.1 q.2
--         ((metricChristoffel g q.1).bilinearComp q.2 q.2))
--       {ρ : ℝ} (hρ : 0 < ρ)
--       (hsource : ∀ q ∈ metricFrameSet g K, ∀ x : Fin 3 → ℝ, ‖x‖ < ρ → normalWaveEquiv x ∈ (e q).source) :
--       ∃ r > 0, ∃ ψ : NormalWaveParameter × NormalWaveSpace → NormalWaveSpace,
--         ContDiff ℝ ∞ ψ ∧ (∀ q ∈ metricFrameSet g K, ψ (q,0) = 0) ∧
--         (∀ q ∈ metricFrameSet g K, q.2.comp (fderiv ℝ (fun t => ψ (q,t)) 0) =
--           ContinuousLinearMap.id ℝ NormalWaveSpace) ∧
--         (∀ q ∈ metricFrameSet g K, ∀ t ∈ Metric.ball (0 : NormalWaveSpace) r,
--           ψ (q,t) ∈ (e q).source ∧ e q (ψ (q,t)) = q.1+t ∧
--           (e q).symm (q.1+t) = ψ (q,t))
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.NormalWaveParameter`, `OAI.YauCounterexamples.NormalWaveSpace`, `OAI.YauCounterexamples.metricChristoffel` and `OAI.YauCounterexamples.normalWaveEquiv` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.normalJetMap` (definitions bundle `OAIQ070A004` of this split); `OAI.YauCounterexamples.metricFrameSet` (definitions bundle `OAIQ070A007` of this split); `OAI.YauCounterexamples.SmoothMetric` (the published bundle `Def_SmoothYau`).
--
--   **Used by.** The proofs of `OAI_YauCounterexamples_uniform_coordinate_packets_common_slope_supported` and `OAI.YauCounterexamples.uniform_coordinate_packets_with_endpoint_ratios_supported` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/CenteredNormalInverseFderiv.lean (declaration OAI.YauCounterexamples.centered_inverse_for_normal_charts)

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
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem centered_inverse_for_normal_charts
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace) {K : Set NormalWaveSpace} (hK : IsCompact K)
    (e : NormalWaveParameter → OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace)
    (he : ∀ q, (e q : NormalWaveSpace → NormalWaveSpace) = normalJetMap q.1 q.2
      ((metricChristoffel g q.1).bilinearComp q.2 q.2))
    {ρ : ℝ} (hρ : 0 < ρ)
    (hsource : ∀ q ∈ metricFrameSet g K, ∀ x : Fin 3 → ℝ, ‖x‖ < ρ → normalWaveEquiv x ∈ (e q).source) :
    ∃ r > 0, ∃ ψ : NormalWaveParameter × NormalWaveSpace → NormalWaveSpace,
      ContDiff ℝ ∞ ψ ∧ (∀ q ∈ metricFrameSet g K, ψ (q,0) = 0) ∧
      (∀ q ∈ metricFrameSet g K, q.2.comp (fderiv ℝ (fun t => ψ (q,t)) 0) =
        ContinuousLinearMap.id ℝ NormalWaveSpace) ∧
      (∀ q ∈ metricFrameSet g K, ∀ t ∈ Metric.ball (0 : NormalWaveSpace) r,
        ψ (q,t) ∈ (e q).source ∧ e q (ψ (q,t)) = q.1+t ∧
        (e q).symm (q.1+t) = ψ (q,t)) := by
  sorry
end YauCounterexamples
end

end OAI
end
