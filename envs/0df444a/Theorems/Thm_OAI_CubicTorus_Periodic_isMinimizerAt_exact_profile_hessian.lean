-- Prove2me | Theorems.Thm_OAI_CubicTorus_Periodic_isMinimizerAt_exact_profile_hessian
-- name    : OAI.CubicTorus.Periodic.isMinimizerAt_exact_profile_hessian
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:48:10.174054+00:00
-- url     : https://prove2.me/theorems/357255a1-ba83-47bf-99cd-47f1d02a7dc1
-- title:
--   OAI.CubicTorus.Periodic.isMinimizerAt_exact_profile_hessian: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.Periodic.isMinimizerAt_exact_profile_hessian` of [lean/OAI/Geometry/CubicTorus/Estimates/TubeCalibration.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/TubeCalibration.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus.Periodic`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_exact_profile_hessian {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
--       ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover) (C : ℝ → ℝ),
--         IsNormalMeasure E μ ∧ ContDiff ℝ (⊤ : ℕ∞) N ∧
--         (∀ m x,N (x+latticeVector m)=N x) ∧
--         (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover) ∧
--           (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1)) ∧
--         (∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
--           (∀ m x,F (x+latticeVector m)=F x) →
--           (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
--             H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) ∧
--         Reduction.UpperSupport isoperimetricProfile C V ∧ deriv C V=H/2 ∧
--         (isoperimetricProfile V)^2*deriv (deriv C) V=
--           -(∫ z,coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1)) ∂(μ : Measure NormalBundle))/8
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.coverTrace`, `OAI.CubicTorus.isoperimetricProfile`, `OAI.CubicTorus.tangentialDivergence` and `OAI.CubicTorus.Reduction.UpperSupport` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus` and `OAI.CubicTorus.latticeVector` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.Periodic.isMinimizerAt_power_affine_spherical`, `OAI.CubicTorus.isMinimizerAt_small_slab_standard` and `OAI.CubicTorus.isoperimetricProfile_power_upper_support` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/TubeCalibration.lean (declaration OAI.CubicTorus.Periodic.isMinimizerAt_exact_profile_hessian)

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000

section

attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

theorem isMinimizerAt_exact_profile_hessian {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover) (C : ℝ → ℝ),
      IsNormalMeasure E μ ∧ ContDiff ℝ (⊤ : ℕ∞) N ∧
      (∀ m x,N (x+latticeVector m)=N x) ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover) ∧
        (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1)) ∧
      (∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
        (∀ m x,F (x+latticeVector m)=F x) →
        (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
          H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) ∧
      Reduction.UpperSupport isoperimetricProfile C V ∧ deriv C V=H/2 ∧
      (isoperimetricProfile V)^2*deriv (deriv C) V=
        -(∫ z,coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1)) ∂(μ : Measure NormalBundle))/8 := by
  sorry

end Periodic
end CubicTorus

end
end

end

end OAI
end
