-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_HilbertSobolev_linear_center_energy_two_jet
-- name    : OAI.TamingCompatibility.HilbertSobolev.linear_center_energy_two_jet
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:12:50.835591+00:00
-- url     : https://prove2.me/theorems/6624048c-2954-456e-a70a-5eda3387628f
-- title:
--   OAI.TamingCompatibility.HilbertSobolev.linear_center_energy_two_jet: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.HilbertSobolev.linear_center_energy_two_jet` of [lean/OAI/Geometry/TamingCompatibility/DifferentialForms/LinearCenterEnergy.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/LinearCenterEnergy.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.HilbertSobolev`, with `open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter LineDeriv Set`, `open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal`):
--
--   ```lean
--   theorem linear_center_energy_two_jet (hdim : Module.finrank ℝ E = 4)
--       {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
--       (d : ι → E) (g : ι → ι → 𝓢(E,ℂ)) (p₀ : E) (A : E ≃L[ℝ] E)
--       (hgp : ∀ i j, principalInBasis (stdOrthonormalBasis ℝ E) (fun i => A (d i))
--         (fun i j => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (g i j)) i j (A p₀) =
--           if i=j then ((((2*Real.pi)^2)⁻¹ : ℝ) : ℂ) else 0)
--       (b : κ → 𝓢(E,ℂ)) (L : κ → F →L[ℂ] F) (v : κ → E)
--       (c : τ → 𝓢(E,ℂ)) (K : τ → F →L[ℂ] F)
--       (ζ : 𝓢(E,ℂ)) (hζ : HasCompactSupport (ζ : E → ℂ))
--       (χ : ℕ → 𝓢(E,ℂ))
--       (hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1)
--       (hζχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1) :
--       ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in 𝓝 (0,p₀), ∀ (hr : 0 < t.1),
--         ∀ (u f : 𝓢(E,F)) (M : ℝ), 0 ≤ M →
--         (∀ k ≤ 3, ∀ m : Fin k → E, (∀ i, ‖m i‖ ≤ 1) → ∀ x,
--           ‖(∂^{m} (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm f)) x‖ ≤ M/t.1^k) →
--         (∀ n ≤ 3, smulLeftCLM F
--           (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A
--             (affineSchwartz (-(t.1⁻¹ • A t.2)) t.1⁻¹ (inv_ne_zero hr.ne') (χ (n+1))))
--           (-directionalPrincipal d g (u : 𝓢'(E,F)) + matrixLowerOrder b L v c K (u : 𝓢'(E,F))) =
--           smulLeftCLM F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A
--             (affineSchwartz (-(t.1⁻¹ • A t.2)) t.1⁻¹ (inv_ne_zero hr.ne') (χ (n+1))))
--             (f : 𝓢'(E,F))) →
--         let U := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm u
--         ∀ x : E, ((χ 4 : E → ℂ) =ᶠ[𝓝 x] fun _ => 1) →
--           t.1*‖U (t.1 • x+A t.2)‖ + t.1^2*∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} U) (t.1 • x+A t.2)‖ +
--             t.1^3*∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ E j} (∂_{stdOrthonormalBasis ℝ E i} U)) (t.1 • x+A t.2)‖ ≤
--           C*(M*t.1^3 + ‖U.toLp 4 (volume : Measure E)‖ +
--             ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} U).toLp 2 (volume : Measure E)‖)
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.HilbertSobolev.directionalPrincipal` and `OAI.TamingCompatibility.HilbertSobolev.matrixLowerOrder` (definitions bundle `OAIQ239Tc001` of this split); `OAI.TamingCompatibility.EuclideanSobolevOperators.affineSchwartz` and `OAI.TamingCompatibility.HilbertSobolev.principalInBasis` (definitions bundle `OAIQ239Tc002` of this split).
--
--   **Used by.** The proofs of `OAI.TamingCompatibility.GeometricHilbert.geometric_center_energy_two_jet` and `OAI.TamingCompatibility.GeometricHilbert.geometric_center_local_energy_two_jet` of this split import it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/LinearCenterEnergy.lean (declaration OAI.TamingCompatibility.HilbertSobolev.linear_center_energy_two_jet)

import Mathlib
import Definitions.Def_OAIQ239Tc001
import Definitions.Def_OAIQ239Tc002

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

theorem linear_center_energy_two_jet (hdim : Module.finrank ℝ E = 4)
    {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
    (d : ι → E) (g : ι → ι → 𝓢(E,ℂ)) (p₀ : E) (A : E ≃L[ℝ] E)
    (hgp : ∀ i j, principalInBasis (stdOrthonormalBasis ℝ E) (fun i => A (d i))
      (fun i j => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (g i j)) i j (A p₀) =
        if i=j then ((((2*Real.pi)^2)⁻¹ : ℝ) : ℂ) else 0)
    (b : κ → 𝓢(E,ℂ)) (L : κ → F →L[ℂ] F) (v : κ → E)
    (c : τ → 𝓢(E,ℂ)) (K : τ → F →L[ℂ] F)
    (ζ : 𝓢(E,ℂ)) (hζ : HasCompactSupport (ζ : E → ℂ))
    (χ : ℕ → 𝓢(E,ℂ))
    (hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1)
    (hζχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in 𝓝 (0,p₀), ∀ (hr : 0 < t.1),
      ∀ (u f : 𝓢(E,F)) (M : ℝ), 0 ≤ M →
      (∀ k ≤ 3, ∀ m : Fin k → E, (∀ i, ‖m i‖ ≤ 1) → ∀ x,
        ‖(∂^{m} (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm f)) x‖ ≤ M/t.1^k) →
      (∀ n ≤ 3, smulLeftCLM F
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A
          (affineSchwartz (-(t.1⁻¹ • A t.2)) t.1⁻¹ (inv_ne_zero hr.ne') (χ (n+1))))
        (-directionalPrincipal d g (u : 𝓢'(E,F)) + matrixLowerOrder b L v c K (u : 𝓢'(E,F))) =
        smulLeftCLM F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A
          (affineSchwartz (-(t.1⁻¹ • A t.2)) t.1⁻¹ (inv_ne_zero hr.ne') (χ (n+1))))
          (f : 𝓢'(E,F))) →
      let U := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm u
      ∀ x : E, ((χ 4 : E → ℂ) =ᶠ[𝓝 x] fun _ => 1) →
        t.1*‖U (t.1 • x+A t.2)‖ + t.1^2*∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} U) (t.1 • x+A t.2)‖ +
          t.1^3*∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ E j} (∂_{stdOrthonormalBasis ℝ E i} U)) (t.1 • x+A t.2)‖ ≤
        C*(M*t.1^3 + ‖U.toLp 4 (volume : Measure E)‖ +
          ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} U).toLp 2 (volume : Measure E)‖) := by
  sorry
end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end
