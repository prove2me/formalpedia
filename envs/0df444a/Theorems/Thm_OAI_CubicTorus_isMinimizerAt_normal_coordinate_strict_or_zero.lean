-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_normal_coordinate_strict_or_zero
-- name    : OAI.CubicTorus.isMinimizerAt_normal_coordinate_strict_or_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:06:46.154735+00:00
-- url     : https://prove2.me/theorems/19ddc375-fee8-4757-95b3-1b1dab479809
-- title:
--   OAI.CubicTorus.isMinimizerAt_normal_coordinate_strict_or_zero: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_normal_coordinate_strict_or_zero` of [lean/OAI/Geometry/CubicTorus/Reflection/MinimizerAxialCenter.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/MinimizerAxialCenter.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_normal_coordinate_strict_or_zero {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
--       (hc : IsPreconnected (frontier (openRepresentative E)))
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
--       {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
--       (hp : ∀ m x,N (x+latticeVector m)=N x)
--       (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (i : Fin 3)
--       (hs : coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
--       [PreconnectedSpace (positiveBoundaryLocus (directionalNormalScalar N hN hp (EuclideanSpace.single i 1))
--         (frontier (openRepresentative E)))] :
--       (∀ a∈frontier (openRepresentative E),N (representative a) i=0) ∨
--       (∀ a∈frontier (openRepresentative E)∩coordinateHalf i 0,0<N (representative a) i) ∨
--       (∀ a∈frontier (openRepresentative E)∩coordinateHalf i 0,N (representative a) i<0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.coordinateHalf`, `OAI.CubicTorus.coordinateReflection`, `OAI.CubicTorus.directionalNormalScalar`, `OAI.CubicTorus.openRepresentative`, `OAI.CubicTorus.positiveBoundaryLocus` and `OAI.CubicTorus.representative` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.latticeVector` and `OAI.CubicTorus.torusVolume` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.isMinimizerAt_connected_reflection_geometry` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/MinimizerAxialCenter.lean (declaration OAI.CubicTorus.isMinimizerAt_normal_coordinate_strict_or_zero)

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

theorem isMinimizerAt_normal_coordinate_strict_or_zero {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (i : Fin 3)
    (hs : coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    [PreconnectedSpace (positiveBoundaryLocus (directionalNormalScalar N hN hp (EuclideanSpace.single i 1))
      (frontier (openRepresentative E)))] :
    (∀ a∈frontier (openRepresentative E),N (representative a) i=0) ∨
    (∀ a∈frontier (openRepresentative E)∩coordinateHalf i 0,0<N (representative a) i) ∨
    (∀ a∈frontier (openRepresentative E)∩coordinateHalf i 0,N (representative a) i<0) := by
  sorry

end CubicTorus

end
end

end OAI
end
