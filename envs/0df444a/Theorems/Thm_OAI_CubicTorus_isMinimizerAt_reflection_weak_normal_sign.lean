-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_reflection_weak_normal_sign
-- name    : OAI.CubicTorus.isMinimizerAt_reflection_weak_normal_sign
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:09:32.514986+00:00
-- url     : https://prove2.me/theorems/18a58aae-79a0-43ba-a572-3e8ac85abbd2
-- title:
--   OAI.CubicTorus.isMinimizerAt_reflection_weak_normal_sign: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_reflection_weak_normal_sign` of [lean/OAI/Geometry/CubicTorus/Reflection/SiblingAxialProjection.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/SiblingAxialProjection.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_reflection_weak_normal_sign {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       (hc : IsPreconnected (frontier (openRepresentative E)))
--       (hR : E=ᵐ[torusVolume](torusFirstReflection ⁻¹' E))
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
--       {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
--       (hp : ∀ m x,N (x+latticeVector m)=N x)
--       (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
--       (∀ x∈frontier (openRepresentative E),firstSeamFunction (representative x)<0 →
--         N (representative x) 0≤0) ∨
--       (∀ x∈frontier (openRepresentative E),firstSeamFunction (representative x)<0 →
--         0≤N (representative x) 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.firstSeamFunction`, `OAI.CubicTorus.openRepresentative`, `OAI.CubicTorus.representative` and `OAI.CubicTorus.torusFirstReflection` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.latticeVector` and `OAI.CubicTorus.torusVolume` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.isMinimizerAt_axis_strict_normal_sign` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/SiblingAxialProjection.lean (declaration OAI.CubicTorus.isMinimizerAt_reflection_weak_normal_sign)

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

theorem isMinimizerAt_reflection_weak_normal_sign {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    (hR : E=ᵐ[torusVolume](torusFirstReflection ⁻¹' E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    (∀ x∈frontier (openRepresentative E),firstSeamFunction (representative x)<0 →
      N (representative x) 0≤0) ∨
    (∀ x∈frontier (openRepresentative E),firstSeamFunction (representative x)<0 →
      0≤N (representative x) 0) := by
  sorry

end CubicTorus

end
end

end

end OAI
end
