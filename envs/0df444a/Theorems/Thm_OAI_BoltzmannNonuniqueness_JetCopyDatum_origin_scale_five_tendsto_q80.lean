-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_origin_scale_five_tendsto_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.origin_scale_five_tendsto_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:27:22.653839+00:00
-- url     : https://prove2.me/theorems/69f28760-9407-4416-bda8-db39f83419a6
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.origin_scale_five_tendsto_q80: intermediate lemma from OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.origin_scale_five_tendsto` of [lean/OAI/MathematicalPhysics/Boltzmann/Jets/OriginMeshLimit.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Jets/OriginMeshLimit.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum`, with `open MeasureTheory Set Filter`, `open scoped ENNReal Topology`, `open BoltzmannNonuniqueness.FiveGainMap`, `open BoltzmannNonuniqueness.PositiveIteration`, `open BoltzmannNonuniqueness.JetCoreSheet`, `open BoltzmannNonuniqueness.GeometricMesh`, `open BoltzmannNonuniqueness.VelocityWeight`):
--
--   ```lean
--   theorem origin_scale_five_tendsto_q80
--       (hMityagin : Published.Mityagin2020FiveGainParameters)
--       {K α γ qexp a T b Vmax s₀ η d₀ θ δ M : ℝ}
--       (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hq : 0 ≤ qexp)
--       (ha : 0 < a) (hb : 0 < b) (hV : 0 ≤ Vmax)
--       (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
--       (hd₀ : 0 < d₀) (hθ : 0 < θ) (hδ : 0 < δ)
--       (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
--       (hphase : Tendsto (fun n => phase (s₀/r n) η) atTop (𝓝 θ)) (N : ℕ → ℕ)
--       (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2)
--       (states : ℕ → State) (hstates : Tendsto states atTop (𝓝 (t₀,x,v)))
--       (htime : ∀ n, (states n).1 ∈ Icc a T)
--       (S : ℕ → Set Velocity) (hS : ∀ i, MeasurableSet (S i))
--       (hbound : ∀ i w, w ∈ S i → ‖w‖ ≤ Vmax ∧ b ≤ ‖transverse w‖)
--       (hinit : ∀ n, WithLp.toLp 2 (states n).2.2 ∈ S 0)
--       {g : ℕ → Published.KineticPhase → ℝ≥0∞} {B : ℝ≥0∞}
--       (hB : B ≠ ∞) (hg : ∀ n, Measurable (g n)) (hgB : ∀ n z, g n z ≤ B)
--       (hL : ∀ C : Set Published.KineticPhase, IsCompact C →
--         Tendsto (fun n => ∫⁻ z in C, g n z) atTop (𝓝 0)) :
--       Tendsto (fun n => restrictedChain a
--         (originScaleKernel (r n) s₀ η K α γ d₀ qexp δ M (N n) 0)
--         S hS (g n) 0 5 (toKinetic (states n))) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.FiveGainMap.State`, `OAI.BoltzmannNonuniqueness.FiveGainMap.V`, `OAI.BoltzmannNonuniqueness.FiveGainMap.toKinetic`, `OAI.BoltzmannNonuniqueness.GeometricMesh.phase`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.originScaleKernel`, `OAI.BoltzmannNonuniqueness.JetLattice.Lattice`, `OAI.BoltzmannNonuniqueness.Published.KineticPhase`, `OAI.BoltzmannNonuniqueness.Published.SpaceTime`, `OAI.BoltzmannNonuniqueness.Published.Velocity`, `OAI.BoltzmannNonuniqueness.VelocityWeight.Transverse` and `OAI.BoltzmannNonuniqueness.VelocityWeight.transverse` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.PositiveIteration.restrictedChain` and `OAI.BoltzmannNonuniqueness.Published.Mityagin2020FiveGainParameters` (definitions bundle `OAIQ080A002` of this split); `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.JetCopyDatum.selected_five_nonaxial_tendsto_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Jets/OriginMeshLimit.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.origin_scale_five_tendsto)

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002

section

attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.FiveGainMap
open BoltzmannNonuniqueness.PositiveIteration
open BoltzmannNonuniqueness.JetCoreSheet
open BoltzmannNonuniqueness.GeometricMesh
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem origin_scale_five_tendsto_q80
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    {K α γ qexp a T b Vmax s₀ η d₀ θ δ M : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hq : 0 ≤ qexp)
    (ha : 0 < a) (hb : 0 < b) (hV : 0 ≤ Vmax)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hd₀ : 0 < d₀) (hθ : 0 < θ) (hδ : 0 < δ)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hphase : Tendsto (fun n => phase (s₀/r n) η) atTop (𝓝 θ)) (N : ℕ → ℕ)
    (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2)
    (states : ℕ → State) (hstates : Tendsto states atTop (𝓝 (t₀,x,v)))
    (htime : ∀ n, (states n).1 ∈ Icc a T)
    (S : ℕ → Set Velocity) (hS : ∀ i, MeasurableSet (S i))
    (hbound : ∀ i w, w ∈ S i → ‖w‖ ≤ Vmax ∧ b ≤ ‖transverse w‖)
    (hinit : ∀ n, WithLp.toLp 2 (states n).2.2 ∈ S 0)
    {g : ℕ → Published.KineticPhase → ℝ≥0∞} {B : ℝ≥0∞}
    (hB : B ≠ ∞) (hg : ∀ n, Measurable (g n)) (hgB : ∀ n z, g n z ≤ B)
    (hL : ∀ C : Set Published.KineticPhase, IsCompact C →
      Tendsto (fun n => ∫⁻ z in C, g n z) atTop (𝓝 0)) :
    Tendsto (fun n => restrictedChain a
      (originScaleKernel (r n) s₀ η K α γ d₀ qexp δ M (N n) 0)
      S hS (g n) 0 5 (toKinetic (states n))) atTop (𝓝 0) := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end
