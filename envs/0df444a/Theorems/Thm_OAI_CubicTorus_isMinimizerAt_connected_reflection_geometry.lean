-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_connected_reflection_geometry
-- name    : OAI.CubicTorus.isMinimizerAt_connected_reflection_geometry
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:02:19.25503+00:00
-- url     : https://prove2.me/theorems/373e72a2-7a2b-444b-8fd8-308ad6deca65
-- title:
--   OAI.CubicTorus.isMinimizerAt_connected_reflection_geometry: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_connected_reflection_geometry` of [lean/OAI/Geometry/CubicTorus/Reflection/MinimizerAxialCenter.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/MinimizerAxialCenter.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_connected_reflection_geometry {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hmE : IsMinimizerAt V E)
--       (hc : IsPreconnected (frontier (openRepresentative E))) :
--       ∃ (b : Torus) (F : Set Torus) (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
--         (_ : ContDiff ℝ (⊤ : ℕ∞) N) (_ : ∀ m x,N (x+latticeVector m)=N x),
--         MeasurableSet F ∧ F =ᵐ[torusVolume] ((fun z => z+b) ⁻¹' E) ∧ IsMinimizerAt V F ∧
--         IsPreconnected (frontier (openRepresentative F)) ∧
--         IsNormalMeasure F μ ∧ (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
--         (∀ i : Fin 3,coordinateReflection i ⁻¹' F =ᵐ[torusVolume] F) ∧
--         (∀ a : Torus,(∀ i,coordinateSine i (representative a)=0) → a∉frontier (openRepresentative F)) ∧
--         ∀ i : Fin 3,(∀ a∈frontier (openRepresentative F),N (representative a) i=0) ∨
--           (∀ a∈frontier (openRepresentative F)∩coordinateHalf i 0,0<N (representative a) i) ∨
--           (∀ a∈frontier (openRepresentative F)∩coordinateHalf i 0,N (representative a) i<0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.coordinateHalf`, `OAI.CubicTorus.coordinateReflection`, `OAI.CubicTorus.coordinateSine`, `OAI.CubicTorus.openRepresentative` and `OAI.CubicTorus.representative` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.latticeVector` and `OAI.CubicTorus.torusVolume` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.isMinimizerAt_standard_or_strict_reflection` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/MinimizerAxialCenter.lean (declaration OAI.CubicTorus.isMinimizerAt_connected_reflection_geometry)

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

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_connected_reflection_geometry {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmE : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E))) :
    ∃ (b : Torus) (F : Set Torus) (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
      (_ : ContDiff ℝ (⊤ : ℕ∞) N) (_ : ∀ m x,N (x+latticeVector m)=N x),
      MeasurableSet F ∧ F =ᵐ[torusVolume] ((fun z => z+b) ⁻¹' E) ∧ IsMinimizerAt V F ∧
      IsPreconnected (frontier (openRepresentative F)) ∧
      IsNormalMeasure F μ ∧ (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ i : Fin 3,coordinateReflection i ⁻¹' F =ᵐ[torusVolume] F) ∧
      (∀ a : Torus,(∀ i,coordinateSine i (representative a)=0) → a∉frontier (openRepresentative F)) ∧
      ∀ i : Fin 3,(∀ a∈frontier (openRepresentative F),N (representative a) i=0) ∨
        (∀ a∈frontier (openRepresentative F)∩coordinateHalf i 0,0<N (representative a) i) ∨
        (∀ a∈frontier (openRepresentative F)∩coordinateHalf i 0,N (representative a) i<0) := by
  sorry

end CubicTorus

end
end

end OAI
end
