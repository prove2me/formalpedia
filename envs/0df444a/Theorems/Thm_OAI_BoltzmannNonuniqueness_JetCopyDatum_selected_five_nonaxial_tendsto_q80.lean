-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_selected_five_nonaxial_tendsto_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.selected_five_nonaxial_tendsto_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:28:11.599311+00:00
-- url     : https://prove2.me/theorems/4334ef1d-dd3b-425d-af38-c0fba872aafb
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.selected_five_nonaxial_tendsto_q80: intermediate lemma from OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.selected_five_nonaxial_tendsto` of [lean/OAI/MathematicalPhysics/Boltzmann/Compactness/SelectedNonaxialLimit.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Compactness/SelectedNonaxialLimit.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum`, with `open MeasureTheory Set Filter`, `open scoped ENNReal Topology`, `open BoltzmannNonuniqueness.FiveGainMap`, `open BoltzmannNonuniqueness.PositiveIteration`, `open BoltzmannNonuniqueness.GeometricMesh`, `open BoltzmannNonuniqueness.VelocityWeight`):
--
--   ```lean
--   theorem selected_five_nonaxial_tendsto_q80
--       (hMityagin : Published.Mityagin2020FiveGainParameters)
--       {K α γ q a T R₀ b₀ X s₀ η d₀ θ : ℝ}
--       (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
--       (ha : 0 < a) (hR₀ : 0 < R₀) (hb₀ : 0 < b₀)
--       (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
--       (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1) (hθ : 0 < θ)
--       (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
--       (hphase : Tendsto (fun n => phase (s₀/r n) η) atTop (𝓝 θ)) (N : ℕ → ℕ)
--       (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2)
--       (states : ℕ → State) (hstates : Tendsto states atTop (𝓝 (t₀,x,v)))
--       (htime : ∀ n, (states n).1 ∈ Icc a T)
--       (hposition : ∀ n, ‖WithLp.toLp 2 (states n).2.1‖ ≤ X)
--       (hvelocity : ∀ n, WithLp.toLp 2 (states n).2.2 ∈ velocityWindow R₀ b₀)
--       {g : ℕ → Published.KineticPhase → ℝ≥0∞} {B : ℝ≥0∞}
--       (hB : B ≠ ∞) (hg : ∀ n, Measurable (g n)) (hgB : ∀ n z, g n z ≤ B)
--       (hL : ∀ C : Set Published.KineticPhase, IsCompact C →
--         Tendsto (fun n => ∫⁻ z in C, g n z) atTop (𝓝 0)) :
--       Tendsto (fun n => iterate a (selectedFreeKernel (r n) s₀ η K α γ d₀ q (N n))
--         (g n) 5 (toKinetic (states n))) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.FiveGainMap.State`, `OAI.BoltzmannNonuniqueness.FiveGainMap.V`, `OAI.BoltzmannNonuniqueness.FiveGainMap.toKinetic`, `OAI.BoltzmannNonuniqueness.GeometricMesh.phase`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedFreeKernel`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.velocityWindow`, `OAI.BoltzmannNonuniqueness.Published.KineticPhase`, `OAI.BoltzmannNonuniqueness.Published.SpaceTime` and `OAI.BoltzmannNonuniqueness.Published.Velocity` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.PositiveIteration.iterate` and `OAI.BoltzmannNonuniqueness.Published.Mityagin2020FiveGainParameters` (definitions bundle `OAIQ080A002` of this split); `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proofs of `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.exists_positive_seed_q80` and `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.full_vanishing_impossible_q80` of this split import it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Compactness/SelectedNonaxialLimit.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.selected_five_nonaxial_tendsto)

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002

section

attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite
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
open BoltzmannNonuniqueness.GeometricMesh
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

attribute [local irreducible] selectedFreeKernel retainedFreeKernel awayOriginKernel

theorem selected_five_nonaxial_tendsto_q80
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    {K α γ q a T R₀ b₀ X s₀ η d₀ θ : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hR₀ : 0 < R₀) (hb₀ : 0 < b₀)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1) (hθ : 0 < θ)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hphase : Tendsto (fun n => phase (s₀/r n) η) atTop (𝓝 θ)) (N : ℕ → ℕ)
    (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2)
    (states : ℕ → State) (hstates : Tendsto states atTop (𝓝 (t₀,x,v)))
    (htime : ∀ n, (states n).1 ∈ Icc a T)
    (hposition : ∀ n, ‖WithLp.toLp 2 (states n).2.1‖ ≤ X)
    (hvelocity : ∀ n, WithLp.toLp 2 (states n).2.2 ∈ velocityWindow R₀ b₀)
    {g : ℕ → Published.KineticPhase → ℝ≥0∞} {B : ℝ≥0∞}
    (hB : B ≠ ∞) (hg : ∀ n, Measurable (g n)) (hgB : ∀ n z, g n z ≤ B)
    (hL : ∀ C : Set Published.KineticPhase, IsCompact C →
      Tendsto (fun n => ∫⁻ z in C, g n z) atTop (𝓝 0)) :
    Tendsto (fun n => iterate a (selectedFreeKernel (r n) s₀ η K α γ d₀ q (N n))
      (g n) 5 (toKinetic (states n))) atTop (𝓝 0) := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end
