-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_normal_curvature_nonnegative
-- name    : OAI.CubicTorus.isMinimizerAt_normal_curvature_nonnegative
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:07:37.296059+00:00
-- url     : https://prove2.me/theorems/f5fcee06-0ff5-4c25-b32f-048804344461
-- title:
--   OAI.CubicTorus.isMinimizerAt_normal_curvature_nonnegative: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_normal_curvature_nonnegative` of [lean/OAI/Geometry/CubicTorus/Regularity/GraphNormalExtensionDivergence.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Regularity/GraphNormalExtensionDivergence.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_normal_curvature_nonnegative {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
--       {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
--       (hp : ∀ m x,N (x+latticeVector m)=N x)
--       (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
--       (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E))
--       (hu : ∀ᶠ y in 𝓝 x,‖N y‖=1) :
--       0 ≤ coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.coverTrace` and `OAI.CubicTorus.openRepresentative` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.latticeVector` and `OAI.CubicTorus.quotientMap` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.Periodic.isMinimizerAt_H1_translation_jacobi`, `OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_zero_curvature`, `OAI.CubicTorus.Periodic.isMinimizerAt_normal_support_jets`, `OAI.CubicTorus.isMinimizerAt_connected_curvature_integral_pos`, `OAI_CubicTorus_isMinimizerAt_cylinder_contact_bounds`, `OAI_CubicTorus_isMinimizerAt_cylinder_contact_nonstandard_star`, `OAI_CubicTorus_isMinimizerAt_exists_coordinate_symmetries_measurable`, `OAI_CubicTorus_isMinimizerAt_first_transition_any_corner_excluded`, `OAI_CubicTorus_isMinimizerAt_missing_neighbor_area_flux`, `OAI_CubicTorus_isMinimizerAt_nonstandard_strict_signs_of_actual_normal`, `OAI_CubicTorus_isMinimizerAt_normal_strong_minimum` and `OAI_CubicTorus_isMinimizerAt_second_transition_standard` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Regularity/GraphNormalExtensionDivergence.lean (declaration OAI.CubicTorus.isMinimizerAt_normal_curvature_nonnegative)

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

theorem isMinimizerAt_normal_curvature_nonnegative {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E))
    (hu : ∀ᶠ y in 𝓝 x,‖N y‖=1) :
    0 ≤ coverTrace ((fderiv ℝ N x).comp (fderiv ℝ N x)) := by
  sorry

end CubicTorus

end
end

end

end OAI
end
