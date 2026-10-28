-- Prove2me | Theorems.Thm_OAI_CubicTorus_Periodic_isMinimizerAt_global_normal_stability
-- name    : OAI.CubicTorus.Periodic.isMinimizerAt_global_normal_stability
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:48:07.238655+00:00
-- url     : https://prove2.me/theorems/856224bb-7e07-4c10-bdfb-fb95cefba47a
-- title:
--   OAI.CubicTorus.Periodic.isMinimizerAt_global_normal_stability: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.Periodic.isMinimizerAt_global_normal_stability` of [lean/OAI/Geometry/CubicTorus/Estimates/GraphInverseMetric.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/GraphInverseMetric.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus.Periodic`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_global_normal_stability {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
--       ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover),
--         IsNormalMeasure E μ ∧ ContDiff ℝ (⊤ : ℕ∞) N ∧
--         (∀ m x,N (x+latticeVector m)=N x) ∧
--         (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover) ∧
--           (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1) ∧ divergence N z.1=H) ∧
--         ∀ f : Cover → ℝ,ContDiff ℝ (⊤ : ℕ∞) f →
--           (∀ m x,f (x+latticeVector m)=f x) →
--           (∫ z,f z.1 ∂(μ : Measure NormalBundle))=0 →
--           0≤normalExtensionJacobi μ f N
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere` and `OAI.CubicTorus.normalExtensionJacobi` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.divergence` and `OAI.CubicTorus.latticeVector` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.Periodic.isMinimizerAt_H1_translation_jacobi`, `OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_zero_curvature`, `OAI.CubicTorus.isMinimizerAt_oriented_CMC_charts` and `OAI.CubicTorus.isMinimizerAt_zero_coordinate_cylindrical` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/GraphInverseMetric.lean (declaration OAI.CubicTorus.Periodic.isMinimizerAt_global_normal_stability)

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

theorem isMinimizerAt_global_normal_stability {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover),
      IsNormalMeasure E μ ∧ ContDiff ℝ (⊤ : ℕ∞) N ∧
      (∀ m x,N (x+latticeVector m)=N x) ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover) ∧
        (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1) ∧ divergence N z.1=H) ∧
      ∀ f : Cover → ℝ,ContDiff ℝ (⊤ : ℕ∞) f →
        (∀ m x,f (x+latticeVector m)=f x) →
        (∫ z,f z.1 ∂(μ : Measure NormalBundle))=0 →
        0≤normalExtensionJacobi μ f N := by
  sorry

end Periodic
end CubicTorus

end
end

end

end OAI
end
