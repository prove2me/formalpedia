-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_curvePolicy_real_tube_probability
-- name    : OAI.DirectionalTransience.curvePolicy_real_tube_probability
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:58:50.899872+00:00
-- url     : https://prove2.me/theorems/adc3e56e-ee2c-4078-812e-08efd4eb0b6f
-- title:
--   OAI.DirectionalTransience.curvePolicy_real_tube_probability: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.curvePolicy_real_tube_probability` of [lean/OAI/Probability/Ballisticity/Geometry/TubeHeightMono.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Geometry/TubeHeightMono.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal Topology Classical`):
--
--   ```lean
--   lemma curvePolicy_real_tube_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
--       (e f : Direction d) (b : ℕ → ℝ) {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
--       {H : ℕ} (hH : 0 < H) {r : ℝ} (hr : 0 < r)
--       (hb : ∀ j ≤ H, |b j-(j:ℝ)*b H/H| ≤ D)
--       (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
--       (hδ1 : δ ≤ 1) (hα1 : α ≤ 1)
--       (dummy : Lattice d) (hd : signedHeight e dummy=H) (hdb : signedCoordinate f dummy=b H)
--       (n : ℕ) {K : ℕ} (hK : 0 < K) (hKn : K ≤ n*H) :
--       let μ := curvePolicy_average ν (realPosition (step e)) f b B hH E hδ hα dummy
--       let θ := (∫ u, signedCoordinate f u ∂μ.toMeasure)/(H:ℝ)
--       (environmentLaw ν).real {ω | quenchedKernel (ω,0)
--         (TubePrefix (realPosition (step e)) f 0 θ (r+2*B+D) K) < (α*δ)^n/2} ≤
--         2*((n:ℝ)*(environmentLaw ν).real {ω | curveIncrement (realPosition (step e)) f 0 b B H ω Set.univ < δ} +
--           (4*(n:ℝ)*(∫ u, (signedCoordinate f u-b H)^2 ∂μ.toMeasure))/r^2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.quenchedKernel`, `OAI.DirectionalTransience.signedCoordinate` and `OAI.DirectionalTransience.signedHeight` (definitions bundle `OAIQ242Bal000` of this split); `OAI.DirectionalTransience.TubePrefix` (definitions bundle `OAIQ242Bal002` of this split); `OAI.DirectionalTransience.curveIncrement` (definitions bundle `OAIQ242Bal003` of this split); `OAI.DirectionalTransience.curvePolicy_average` (definitions bundle `OAIQ242Bal005` of this split); `OAI.DirectionalTransience.Direction`, `OAI.DirectionalTransience.Environment`, `OAI.DirectionalTransience.Lattice`, `OAI.DirectionalTransience.Path`, `OAI.DirectionalTransience.Row`, `OAI.DirectionalTransience.State`, `OAI.DirectionalTransience.environmentLaw`, `OAI.DirectionalTransience.realPosition` and `OAI.DirectionalTransience.step` (the published bundle `Def_DirectionalBallisticity`).
--
--   **Used by.** The proof of `OAI.DirectionalTransience.clipping_uniform` of this split imports it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Geometry/TubeHeightMono.lean (declaration OAI.DirectionalTransience.curvePolicy_real_tube_probability)

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal005

section

attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma curvePolicy_real_tube_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (b : ℕ → ℝ) {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    {H : ℕ} (hH : 0 < H) {r : ℝ} (hr : 0 < r)
    (hb : ∀ j ≤ H, |b j-(j:ℝ)*b H/H| ≤ D)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (hδ1 : δ ≤ 1) (hα1 : α ≤ 1)
    (dummy : Lattice d) (hd : signedHeight e dummy=H) (hdb : signedCoordinate f dummy=b H)
    (n : ℕ) {K : ℕ} (hK : 0 < K) (hKn : K ≤ n*H) :
    let μ := curvePolicy_average ν (realPosition (step e)) f b B hH E hδ hα dummy
    let θ := (∫ u, signedCoordinate f u ∂μ.toMeasure)/(H:ℝ)
    (environmentLaw ν).real {ω | quenchedKernel (ω,0)
      (TubePrefix (realPosition (step e)) f 0 θ (r+2*B+D) K) < (α*δ)^n/2} ≤
      2*((n:ℝ)*(environmentLaw ν).real {ω | curveIncrement (realPosition (step e)) f 0 b B H ω Set.univ < δ} +
        (4*(n:ℝ)*(∫ u, (signedCoordinate f u-b H)^2 ∂μ.toMeasure))/r^2) := by
  sorry

end DirectionalTransience

end

end

end OAI
end
