-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_slice_absolutelyContinuous
-- name    : OAI.CubicTorus.isMinimizerAt_slice_absolutelyContinuous
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:10:43.053641+00:00
-- url     : https://prove2.me/theorems/c90c52ab-de2c-4a61-822e-8d762e1cd32f
-- title:
--   OAI.CubicTorus.isMinimizerAt_slice_absolutelyContinuous: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_slice_absolutelyContinuous` of [lean/OAI/Geometry/CubicTorus/Reflection/ActualAxialFlux.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/ActualAxialFlux.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_slice_absolutelyContinuous {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
--       (i : Fin 3) (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
--       (∀ a b,AbsolutelyContinuousOnInterval
--         (fun t : ℝ ↦ (axialSliceVolume (openRepresentative E) i (t : AxisCircle)).toReal) a b) ∧
--       ∀ᵐ t : ℝ,t∈Icc (0 : ℝ) 1 → HasDerivAt
--         (fun t : ℝ ↦ (axialSliceVolume (openRepresentative E) i (t : AxisCircle)).toReal)
--         (-axialNormalDensity μ i (t : AxisCircle)) t
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.AxisCircle`, `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.axialAreaMarginal`, `OAI.CubicTorus.axialNormalDensity`, `OAI.CubicTorus.axialSliceVolume` and `OAI.CubicTorus.openRepresentative` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt` and `OAI.CubicTorus.Torus` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.isMinimizerAt_measurable_weighted_area_bound` and `OAI.CubicTorus.isMinimizerAt_missing_neighbor_projection` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/ActualAxialFlux.lean (declaration OAI.CubicTorus.isMinimizerAt_slice_absolutelyContinuous)

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

theorem isMinimizerAt_slice_absolutelyContinuous {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (i : Fin 3) (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    (∀ a b,AbsolutelyContinuousOnInterval
      (fun t : ℝ ↦ (axialSliceVolume (openRepresentative E) i (t : AxisCircle)).toReal) a b) ∧
    ∀ᵐ t : ℝ,t∈Icc (0 : ℝ) 1 → HasDerivAt
      (fun t : ℝ ↦ (axialSliceVolume (openRepresentative E) i (t : AxisCircle)).toReal)
      (-axialNormalDensity μ i (t : AxisCircle)) t := by
  sorry

end CubicTorus

end
end

end

end OAI
end
