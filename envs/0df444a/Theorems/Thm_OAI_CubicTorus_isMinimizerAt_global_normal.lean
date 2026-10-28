-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_global_normal
-- name    : OAI.CubicTorus.isMinimizerAt_global_normal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:05:15.6431+00:00
-- url     : https://prove2.me/theorems/364802cb-1df0-4223-82cb-dd505035dcb8
-- title:
--   OAI.CubicTorus.isMinimizerAt_global_normal: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_global_normal` of [lean/OAI/Geometry/CubicTorus/Estimates/GraphInverseMetric.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/GraphInverseMetric.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_global_normal {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
--       ∃ N : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) N ∧
--         (∀ m x,N (x+latticeVector m)=N x) ∧
--         ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover) ∧
--           (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle` and `OAI.CubicTorus.NormalSphere` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus` and `OAI.CubicTorus.latticeVector` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.Periodic.isMinimizerAt_full_jacobi_system`, `OAI.CubicTorus.Periodic.isMinimizerAt_global_normal_stability`, `OAI.CubicTorus.Periodic.isMinimizerAt_normal_support_jets`, `OAI.CubicTorus.Periodic.profile_hessian_of_CMC`, `OAI_CubicTorus_isMinimizerAt_cylinder_contact_bounds`, `OAI_CubicTorus_isMinimizerAt_cylinder_contact_nonstandard_star`, `OAI_CubicTorus_isMinimizerAt_exists_coordinate_symmetries_measurable`, `OAI_CubicTorus_isMinimizerAt_first_transition_any_corner_excluded`, `OAI_CubicTorus_isMinimizerAt_missing_neighbor_area_flux`, `OAI.CubicTorus.isMinimizerAt_missing_neighbor_seam_bound`, `OAI.CubicTorus.isMinimizerAt_nonstandard_integrated_flux`, `OAI_CubicTorus_isMinimizerAt_nonstandard_strict_signs_of_actual_normal`, `OAI_CubicTorus_isMinimizerAt_normal_strong_minimum` and `OAI_CubicTorus_isMinimizerAt_second_transition_standard` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/GraphInverseMetric.lean (declaration OAI.CubicTorus.isMinimizerAt_global_normal)

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

theorem isMinimizerAt_global_normal {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ N : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) N ∧
      (∀ m x,N (x+latticeVector m)=N x) ∧
      ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover) ∧
        (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1) := by
  sorry

end CubicTorus

end
end

end

end OAI
end
