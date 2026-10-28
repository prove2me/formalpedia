-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_nonstandard_strict_octant
-- name    : OAI.CubicTorus.isMinimizerAt_nonstandard_strict_octant
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:33:52.38448+00:00
-- url     : https://prove2.me/theorems/c620357f-1f61-4a21-851c-5f93dc84f52d
-- title:
--   OAI.CubicTorus.isMinimizerAt_nonstandard_strict_octant: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_nonstandard_strict_octant` of [lean/OAI/Geometry/CubicTorus/Profiles/OctantVertex.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/OctantVertex.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_nonstandard_strict_octant {V : ℝ} (hV : V∈Ioc 0 (1/2))
--       {E : Set Torus} (hmin : IsMinimizerAt V E)
--       (hc : IsPreconnected (frontier (openRepresentative E)))
--       (hstd : ¬StandardRegionAt V E)
--       (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E)) :
--       ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover) (b : Fin 3 → Bool),
--         IsNormalMeasure E μ ∧ ContDiff ℝ (⊤ : ℕ∞) N ∧
--         (∀ m x,N (x+latticeVector m)=N x) ∧
--         (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
--         (∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
--           (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H) ∧
--         (∀ i : Fin 3,∀ x : Cover,x i∈Ioo (1/2 : ℝ) 1 →
--           quotientMap x∈frontier (openRepresentative E) →
--           if b i then 0<N x i else N x i<0) ∧
--         (∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
--           quotientMap y∈openRepresentative E → quotientMap x∈openRepresentative E)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.OrientedCoordinateLE`, `OAI.CubicTorus.axisReflection`, `OAI.CubicTorus.openRepresentative` and `OAI.CubicTorus.LatticeIsometry` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.upperOctant` (definitions bundle `OAIQ079A003` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.StandardRegionAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.divergence`, `OAI.CubicTorus.latticeVector`, `OAI.CubicTorus.quotientMap` and `OAI.CubicTorus.torusVolume` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.isMinimizerAt_nonstandard_integrated_flux` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/OctantVertex.lean (declaration OAI.CubicTorus.isMinimizerAt_nonstandard_strict_octant)

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003

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

theorem isMinimizerAt_nonstandard_strict_octant {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    (hstd : ¬StandardRegionAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E)) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover) (b : Fin 3 → Bool),
      IsNormalMeasure E μ ∧ ContDiff ℝ (⊤ : ℕ∞) N ∧
      (∀ m x,N (x+latticeVector m)=N x) ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
        (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H) ∧
      (∀ i : Fin 3,∀ x : Cover,x i∈Ioo (1/2 : ℝ) 1 →
        quotientMap x∈frontier (openRepresentative E) →
        if b i then 0<N x i else N x i<0) ∧
      (∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
        quotientMap y∈openRepresentative E → quotientMap x∈openRepresentative E) := by
  sorry

end CubicTorus

end
end

end

end OAI
end
