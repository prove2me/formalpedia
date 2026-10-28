-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_nonstandard_integrated_flux
-- name    : OAI.CubicTorus.isMinimizerAt_nonstandard_integrated_flux
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:05:57.885904+00:00
-- url     : https://prove2.me/theorems/b9d19965-4cb4-4f40-b94c-f13ae5ce665c
-- title:
--   OAI.CubicTorus.isMinimizerAt_nonstandard_integrated_flux: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_nonstandard_integrated_flux` of [lean/OAI/Geometry/CubicTorus/Profiles/NestingBaseline.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/NestingBaseline.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_nonstandard_integrated_flux {V : ℝ} (hV : V∈Ioc 0 (1/2))
--       {E : Set Torus} (hmin : IsMinimizerAt V E) (hstd : ¬StandardRegionAt V E)
--       (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E)) :
--       ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ),IsNormalMeasure E μ ∧
--         (∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
--           (∀ m x,F (x+latticeVector m)=F x) →
--           (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
--             H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) ∧
--         (∀ i : Fin 3,(axialAreaMarginal μ i : Measure AxisCircle)≪volume) ∧
--         ∀ i : Fin 3,Nesting.lambda*axialTransverseMass μ i+
--           (∫ t,Nesting.weight (actualAxialFlux (openRepresentative E) μ H i t/
--             axialPerimeterDensity μ i t)*|axialNormalDensity μ i t|)≤(perimeter E).toReal
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.AxisCircle`, `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.actualAxialFlux`, `OAI.CubicTorus.axialAreaMarginal`, `OAI.CubicTorus.axialNormalDensity`, `OAI.CubicTorus.axialPerimeterDensity`, `OAI.CubicTorus.axialTransverseMass`, `OAI.CubicTorus.axisReflection`, `OAI.CubicTorus.openRepresentative`, `OAI.CubicTorus.tangentialDivergence`, `OAI.CubicTorus.LatticeIsometry`, `OAI.CubicTorus.Nesting.lambda` and `OAI.CubicTorus.Nesting.weight` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.StandardRegionAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.latticeVector`, `OAI.CubicTorus.perimeter` and `OAI.CubicTorus.torusVolume` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI_CubicTorus_isMinimizerAt_cylinder_contact_nonstandard_star`, `OAI.CubicTorus.isMinimizerAt_cylinder_contact_standard` and `OAI.CubicTorus.isMinimizerAt_fixed_downset_not_three_vertices` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/NestingBaseline.lean (declaration OAI.CubicTorus.isMinimizerAt_nonstandard_integrated_flux)

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

theorem isMinimizerAt_nonstandard_integrated_flux {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hmin : IsMinimizerAt V E) (hstd : ¬StandardRegionAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E)) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ),IsNormalMeasure E μ ∧
      (∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
        (∀ m x,F (x+latticeVector m)=F x) →
        (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
          H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) ∧
      (∀ i : Fin 3,(axialAreaMarginal μ i : Measure AxisCircle)≪volume) ∧
      ∀ i : Fin 3,Nesting.lambda*axialTransverseMass μ i+
        (∫ t,Nesting.weight (actualAxialFlux (openRepresentative E) μ H i t/
          axialPerimeterDensity μ i t)*|axialNormalDensity μ i t|)≤(perimeter E).toReal := by
  sorry

end CubicTorus

end
end

end

end OAI
end
