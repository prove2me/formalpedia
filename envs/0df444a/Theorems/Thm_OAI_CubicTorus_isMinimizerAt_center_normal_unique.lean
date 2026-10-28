-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_center_normal_unique
-- name    : OAI.CubicTorus.isMinimizerAt_center_normal_unique
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:00:35.262355+00:00
-- url     : https://prove2.me/theorems/f748b71a-ef73-42e2-a249-a6966cc32127
-- title:
--   OAI.CubicTorus.isMinimizerAt_center_normal_unique: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_center_normal_unique` of [lean/OAI/Geometry/CubicTorus/Reflection/SiblingReflectNormal.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/SiblingReflectNormal.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_center_normal_unique {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E)) :
--       ∃ w : Cover,∀ (μ : FiniteMeasure NormalBundle),IsNormalMeasure E μ →
--         ∀ (N : Cover → Cover),ContDiff ℝ (⊤ : ℕ∞) N →
--         (∀ m x,N (x+latticeVector m)=N x) →
--         (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) → N cubeCenter=w
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.cubeCenter` and `OAI.CubicTorus.openRepresentative` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.latticeVector` and `OAI.CubicTorus.quotientMap` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.isMinimizerAt_axis_strict_normal_sign`, `OAI.CubicTorus.isMinimizerAt_corner_boundary_heights_null`, `OAI.CubicTorus.isMinimizerAt_missing_neighbor_flux_unrestricted`, `OAI.CubicTorus.isMinimizerAt_missing_neighbor_projection`, `OAI.CubicTorus.isMinimizerAt_missing_neighbor_sharp_area_flux`, `OAI.CubicTorus.isMinimizerAt_nesting_cubic_gain`, `OAI.CubicTorus.isMinimizerAt_nonstandard_integrated_flux`, `OAI.CubicTorus.isMinimizerAt_reflection_weak_normal_sign`, `OAI.CubicTorus.isMinimizerAt_three_vertex_bottom`, `OAI.CubicTorus.normal_transverse_near_reflection_height` and `OAI.CubicTorus.strict_normal_component_ne_zero_ae` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/SiblingReflectNormal.lean (declaration OAI.CubicTorus.isMinimizerAt_center_normal_unique)

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000

section

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

theorem isMinimizerAt_center_normal_unique {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E)) :
    ∃ w : Cover,∀ (μ : FiniteMeasure NormalBundle),IsNormalMeasure E μ →
      ∀ (N : Cover → Cover),ContDiff ℝ (⊤ : ℕ∞) N →
      (∀ m x,N (x+latticeVector m)=N x) →
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) → N cubeCenter=w := by
  sorry

end CubicTorus

end
end

end

end OAI
end
