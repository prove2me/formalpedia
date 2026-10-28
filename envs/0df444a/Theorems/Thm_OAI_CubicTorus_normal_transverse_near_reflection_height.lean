-- Prove2me | Theorems.Thm_OAI_CubicTorus_normal_transverse_near_reflection_height
-- name    : OAI.CubicTorus.normal_transverse_near_reflection_height
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:19:14.618387+00:00
-- url     : https://prove2.me/theorems/2536a586-b08e-45b6-9f27-94f61a326ac3
-- title:
--   OAI.CubicTorus.normal_transverse_near_reflection_height: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.normal_transverse_near_reflection_height` of [lean/OAI/Geometry/CubicTorus/Reflection/AxialAreaDensity.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/AxialAreaDensity.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   lemma normal_transverse_near_reflection_height {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       (i : Fin 3) (hR : E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
--       {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
--       (hp : ∀ m x,N (x+latticeVector m)=N x)
--       (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
--       {t : AxisCircle} (ht : -t=t) {c : ℝ} (hc : c∈Ioo 0 1) :
--       ∃ S : Set AxisCircle,IsOpen S ∧ t∈S ∧
--         ∀ᵐ z ∂(μ : Measure NormalBundle),(((z.1 : Cover) i) : AxisCircle)∈S →
--           c*normalTransverseLength i z≤(normalTransverseLength i z)^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.AxisCircle`, `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.axisReflection`, `OAI.CubicTorus.normalTransverseLength` and `OAI.CubicTorus.LatticeIsometry` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.latticeVector` and `OAI.CubicTorus.torusVolume` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.isMinimizerAt_missing_neighbor_seam_bound` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/AxialAreaDensity.lean (declaration OAI.CubicTorus.normal_transverse_near_reflection_height)

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

lemma normal_transverse_near_reflection_height {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (i : Fin 3) (hR : E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {t : AxisCircle} (ht : -t=t) {c : ℝ} (hc : c∈Ioo 0 1) :
    ∃ S : Set AxisCircle,IsOpen S ∧ t∈S ∧
      ∀ᵐ z ∂(μ : Measure NormalBundle),(((z.1 : Cover) i) : AxisCircle)∈S →
        c*normalTransverseLength i z≤(normalTransverseLength i z)^2 := by
  sorry

end CubicTorus

end
end

end

end OAI
end
