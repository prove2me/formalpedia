-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_HilbertSobolev_parameter_energy_two_jet
-- name    : OAI.TamingCompatibility.HilbertSobolev.parameter_energy_two_jet
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:20:26.065719+00:00
-- url     : https://prove2.me/theorems/01644668-1663-4d38-a0f7-5fd5133149c5
-- title:
--   OAI.TamingCompatibility.HilbertSobolev.parameter_energy_two_jet: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.HilbertSobolev.parameter_energy_two_jet` of [lean/OAI/Geometry/TamingCompatibility/DifferentialForms/ParameterEnergyJet.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/ParameterEnergyJet.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.HilbertSobolev`, with `open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter LineDeriv Set`, `open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal`):
--
--   ```lean
--   theorem parameter_energy_two_jet (p₀ : P) (hdim : Module.finrank ℝ E = 4)
--       {ι κ : Type*} [Fintype ι] [Fintype κ]
--       (a : P → basisIndex E → basisIndex E → 𝓢(E,ℂ))
--       (ha : ∀ n ≤ 3, Tendsto (fun r => ‖perturbation (F := F) n (a r)‖) (𝓝 p₀) (𝓝 0))
--       (hac : ∀ n ≤ 3, ∀ i j, ContinuousAt (fun r => coefficientSize n (a r i j)) p₀)
--       (b : P → ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (d : ι → E)
--       (c : P → κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F)
--       (hb : ∀ n ≤ 3, ∀ i, ContinuousAt (fun r => coefficientSize n (b r i)) p₀)
--       (hc : ∀ n ≤ 3, ∀ i, ContinuousAt (fun r => coefficientSize n (c r i)) p₀)
--       (χ : ℕ → 𝓢(E,ℂ))
--       (hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1)
--       (ζ : 𝓢(E,ℂ)) (hζ : HasCompactSupport (ζ : E → ℂ))
--       (hζχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1) :
--       ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in 𝓝 p₀, ∀ (r : ℝ) (hr : 0 < r)
--         (p : E) (u f : 𝓢(E,F)) (M : ℝ), 0 ≤ M →
--         (∀ k ≤ 3, ∀ m : Fin k → E, (∀ i, ‖m i‖ ≤ 1) → ∀ x, ‖(∂^{m} f) x‖ ≤ M/r^k) →
--         (∀ n ≤ 3, smulLeftCLM F (χ (n+1))
--           (perturbedHelmholtz (a t) (rescaleSchwartz p r hr.ne' u : 𝓢'(E,F)) +
--             matrixLowerOrder (b t) L d (c t) K (rescaleSchwartz p r hr.ne' u : 𝓢'(E,F))) =
--           smulLeftCLM F (χ (n+1)) (r^2 • rescaleSchwartz p r hr.ne' f : 𝓢'(E,F))) →
--         ∀ x : E, ((χ 4 : E → ℂ) =ᶠ[𝓝 x] fun _ => 1) →
--           r*‖u (r • x+p)‖ + r^2*∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} u) (r • x+p)‖ +
--             r^3*∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ E j} (∂_{stdOrthonormalBasis ℝ E i} u)) (r • x+p)‖ ≤
--           C*(M*r^3 + ‖u.toLp 4 (volume : Measure E)‖ +
--             ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} u).toLp 2 (volume : Measure E)‖)
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.HilbertSobolev.H` and `OAI.TamingCompatibility.HilbertSobolev.matrixLowerOrder` (definitions bundle `OAIQ239Tc001` of this split); `OAI.TamingCompatibility.HilbertSobolev.basisIndex` and `OAI.TamingCompatibility.HilbertSobolev.coefficientSize` (definitions bundle `OAIQ239Tc002` of this split); `OAI.TamingCompatibility.HilbertSobolev.rescaleSchwartz` (definitions bundle `OAIQ239Tc004` of this split); `OAI.TamingCompatibility.HilbertSobolev.perturbation` and `OAI.TamingCompatibility.HilbertSobolev.perturbedHelmholtz` (definitions bundle `OAIQ239Tc005` of this split).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.HilbertSobolev.linear_center_energy_two_jet` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/ParameterEnergyJet.lean (declaration OAI.TamingCompatibility.HilbertSobolev.parameter_energy_two_jet)

import Mathlib
import Definitions.Def_OAIQ239Tc004
import Definitions.Def_OAIQ239Tc005

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter LineDeriv Set
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {P : Type*} [TopologicalSpace P]

theorem parameter_energy_two_jet (p₀ : P) (hdim : Module.finrank ℝ E = 4)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : P → basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (ha : ∀ n ≤ 3, Tendsto (fun r => ‖perturbation (F := F) n (a r)‖) (𝓝 p₀) (𝓝 0))
    (hac : ∀ n ≤ 3, ∀ i j, ContinuousAt (fun r => coefficientSize n (a r i j)) p₀)
    (b : P → ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (d : ι → E)
    (c : P → κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F)
    (hb : ∀ n ≤ 3, ∀ i, ContinuousAt (fun r => coefficientSize n (b r i)) p₀)
    (hc : ∀ n ≤ 3, ∀ i, ContinuousAt (fun r => coefficientSize n (c r i)) p₀)
    (χ : ℕ → 𝓢(E,ℂ))
    (hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1)
    (ζ : 𝓢(E,ℂ)) (hζ : HasCompactSupport (ζ : E → ℂ))
    (hζχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in 𝓝 p₀, ∀ (r : ℝ) (hr : 0 < r)
      (p : E) (u f : 𝓢(E,F)) (M : ℝ), 0 ≤ M →
      (∀ k ≤ 3, ∀ m : Fin k → E, (∀ i, ‖m i‖ ≤ 1) → ∀ x, ‖(∂^{m} f) x‖ ≤ M/r^k) →
      (∀ n ≤ 3, smulLeftCLM F (χ (n+1))
        (perturbedHelmholtz (a t) (rescaleSchwartz p r hr.ne' u : 𝓢'(E,F)) +
          matrixLowerOrder (b t) L d (c t) K (rescaleSchwartz p r hr.ne' u : 𝓢'(E,F))) =
        smulLeftCLM F (χ (n+1)) (r^2 • rescaleSchwartz p r hr.ne' f : 𝓢'(E,F))) →
      ∀ x : E, ((χ 4 : E → ℂ) =ᶠ[𝓝 x] fun _ => 1) →
        r*‖u (r • x+p)‖ + r^2*∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} u) (r • x+p)‖ +
          r^3*∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ E j} (∂_{stdOrthonormalBasis ℝ E i} u)) (r • x+p)‖ ≤
        C*(M*r^3 + ‖u.toLp 4 (volume : Measure E)‖ +
          ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} u).toLp 2 (volume : Measure E)‖) := by
  sorry
end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end
