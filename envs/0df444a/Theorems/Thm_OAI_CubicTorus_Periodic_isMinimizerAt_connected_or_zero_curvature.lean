-- Prove2me | Theorems.Thm_OAI_CubicTorus_Periodic_isMinimizerAt_connected_or_zero_curvature
-- name    : OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_zero_curvature
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:48:18.345245+00:00
-- url     : https://prove2.me/theorems/e51fb3ba-387f-4eb2-b342-9b8f66f77033
-- title:
--   OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_zero_curvature: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_zero_curvature` of [lean/OAI/Geometry/CubicTorus/Regularity/GraphNormalExtensionDivergence.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Regularity/GraphNormalExtensionDivergence.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus.Periodic`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_connected_or_zero_curvature {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
--       ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover),
--         IsNormalMeasure E μ ∧ ContDiff ℝ (⊤ : ℕ∞) N ∧
--         (∀ m x,N (x+latticeVector m)=N x) ∧
--         (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
--         (∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
--           (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H ∧
--             0 ≤ coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x))) ∧
--         (∀ f : Cover → ℝ,ContDiff ℝ (⊤ : ℕ∞) f →
--           (∀ m x,f (x+latticeVector m)=f x) →
--           (∫ z,f z.1 ∂(μ : Measure NormalBundle))=0 →
--           0≤normalExtensionJacobi μ f N) ∧
--         (IsPreconnected (frontier (openRepresentative E)) ∨
--           ∀ x,quotientMap x∈frontier (openRepresentative E) →
--             coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x))=0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.coverTrace`, `OAI.CubicTorus.normalExtensionJacobi` and `OAI.CubicTorus.openRepresentative` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.divergence`, `OAI.CubicTorus.latticeVector` and `OAI.CubicTorus.quotientMap` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_circle_phase` and `OAI.CubicTorus.isMinimizerAt_reflection_symmetry_of_competitor` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Regularity/GraphNormalExtensionDivergence.lean (declaration OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_zero_curvature)

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

theorem isMinimizerAt_connected_or_zero_curvature {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover),
      IsNormalMeasure E μ ∧ ContDiff ℝ (⊤ : ℕ∞) N ∧
      (∀ m x,N (x+latticeVector m)=N x) ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
        (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H ∧
          0 ≤ coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x))) ∧
      (∀ f : Cover → ℝ,ContDiff ℝ (⊤ : ℕ∞) f →
        (∀ m x,f (x+latticeVector m)=f x) →
        (∫ z,f z.1 ∂(μ : Measure NormalBundle))=0 →
        0≤normalExtensionJacobi μ f N) ∧
      (IsPreconnected (frontier (openRepresentative E)) ∨
        ∀ x,quotientMap x∈frontier (openRepresentative E) →
          coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x))=0) := by
  sorry

end Periodic
end CubicTorus

end
end

end

end OAI
end
