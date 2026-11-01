-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_positive_five_transverse_escape_tendsto_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.positive_five_transverse_escape_tendsto_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:27:47.187516+00:00
-- url     : https://prove2.me/theorems/290329c1-113d-4e59-9102-a49e9c0774c3
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.positive_five_transverse_escape_tendsto_q80: intermediate lemma from OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.positive_five_transverse_escape_tendsto` of [lean/OAI/MathematicalPhysics/Boltzmann/Approximation/PositiveRestrictedChain.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/PositiveRestrictedChain.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum`, with `open MeasureTheory Set Filter`, `open scoped ENNReal Topology`, `open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetLattice`, `open BoltzmannNonuniqueness.PositiveIteration`):
--
--   ```lean
--   theorem positive_five_transverse_escape_tendsto_q80 {K α γ q a T V s₀ η d₀ : ℝ}
--       (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
--       (ha : 0 < a) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
--       (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
--       (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (N : ℕ → ℕ) (z : ℕ → Published.KineticPhase)
--       (ht : ∀ n, (z n).1.1 ∈ Icc a T) (hv : ∀ n, ‖(z n).2‖ ≤ V)
--       (hx : ∀ R : ℝ, ∀ᶠ n in atTop, ∀ k : Lattice,
--         R ≤ ‖transverse ((z n).1.2-(r n)⁻¹ • latticeVector k)‖)
--       {f : ℕ → Published.KineticPhase → ℝ≥0∞} {B : ℝ≥0∞} (hB : B ≠ ∞)
--       (hf : ∀ n y, y.1.1 ∈ Icc a T → f n y ≤ B) :
--       Tendsto (fun n => iterate a (positiveMainKernel (r n) s₀ η K α γ d₀ q (N n))
--         (f n) 5 (z n)) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.JetCopyDatum.latticeVector`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.positiveMainKernel`, `OAI.BoltzmannNonuniqueness.JetLattice.Lattice`, `OAI.BoltzmannNonuniqueness.Published.KineticPhase`, `OAI.BoltzmannNonuniqueness.Published.SpaceTime`, `OAI.BoltzmannNonuniqueness.Published.Velocity`, `OAI.BoltzmannNonuniqueness.VelocityWeight.Transverse` and `OAI.BoltzmannNonuniqueness.VelocityWeight.transverse` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.PositiveIteration.iterate` (definitions bundle `OAIQ080A002` of this split); `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proofs of `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.exists_positive_seed_q80` and `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.full_vanishing_impossible_q80` of this split import it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/PositiveRestrictedChain.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.positive_five_transverse_escape_tendsto)

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002

section

attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem positive_five_transverse_escape_tendsto_q80 {K α γ q a T V s₀ η d₀ : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (N : ℕ → ℕ) (z : ℕ → Published.KineticPhase)
    (ht : ∀ n, (z n).1.1 ∈ Icc a T) (hv : ∀ n, ‖(z n).2‖ ≤ V)
    (hx : ∀ R : ℝ, ∀ᶠ n in atTop, ∀ k : Lattice,
      R ≤ ‖transverse ((z n).1.2-(r n)⁻¹ • latticeVector k)‖)
    {f : ℕ → Published.KineticPhase → ℝ≥0∞} {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hf : ∀ n y, y.1.1 ∈ Icc a T → f n y ≤ B) :
    Tendsto (fun n => iterate a (positiveMainKernel (r n) s₀ η K α γ d₀ q (N n))
      (f n) 5 (z n)) atTop (𝓝 0) := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end
