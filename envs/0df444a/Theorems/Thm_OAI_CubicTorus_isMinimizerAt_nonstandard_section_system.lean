-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_nonstandard_section_system
-- name    : OAI.CubicTorus.isMinimizerAt_nonstandard_section_system
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:06:45.457298+00:00
-- url     : https://prove2.me/theorems/1a553307-204a-45a8-a1ea-6cec6dc5487d
-- title:
--   OAI.CubicTorus.isMinimizerAt_nonstandard_section_system: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_nonstandard_section_system` of [lean/OAI/Geometry/CubicTorus/Reflection/ChamberPositionProducer.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/ChamberPositionProducer.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_nonstandard_section_system {V : ℝ} (hV : V∈Ioc 0 (1/2))
--       {E : Set Torus} (hmE : IsMinimizerAt V E) (hnstd : ¬SmallStandardRegion V E) :
--       ∃ (b : Torus) (F : Set Torus) (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
--         (_ : ContDiff ℝ (⊤ : ℕ∞) N) (_ : ∀ m x,N (x+latticeVector m)=N x)
--         (s : Fin 3 → Bool) (H : ℝ),
--         MeasurableSet F ∧ F =ᵐ[torusVolume] ((fun z => z+b) ⁻¹' E) ∧ IsMinimizerAt V F ∧
--         IsPreconnected (frontier (openRepresentative F)) ∧ IsNormalMeasure F μ ∧
--         (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
--         (∀ i : Fin 3,coordinateReflection i ⁻¹' F =ᵐ[torusVolume] F) ∧
--         (∀ (x : Cover) (i : Fin 3),
--           quotientMap x∈frontier (openRepresentative F)∩coordinateHalf i (if s i then 0 else 1/2) → 0<N x i) ∧
--         (∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
--           H*directionalFlux F D.coordinate D.function) ∧
--         (0<(μ.mass : ℝ)) ∧ (∑ i : Fin 3,axialFluxWeight μ i)=2 ∧
--         (∀ i : Fin 3,0≤axialFluxWeight μ i ∧ axialFluxWeight μ i<1) ∧
--         (∃ i : Fin 3,quotientMap (chamberVertex s (fun j => decide (j=i)))∈closure (openRepresentative F)) ∧
--         (∀ i : Fin 3,Continuous (axialSectionArea (openRepresentative F) i) ∧
--           AntitoneOn (axialSectionArea (openRepresentative F) i)
--             (Icc (chamberCorner s i) (chamberCorner s i+1/2))) ∧
--         (∀ i : Fin 3,
--           2*(axialSectionArea (openRepresentative F) i (chamberCorner s i)-
--             axialSectionArea (openRepresentative F) i (chamberCorner s i+1/2))≤
--             (μ.mass : ℝ)*Real.sqrt (1-axialFluxWeight μ i)) ∧
--         (∀ (i : Fin 3) (a : Bool),
--           axialSlicePerimeter (openRepresentative F) i (if a then 1/2 else 0)=
--             ENNReal.ofReal ((μ.mass : ℝ)*axialFluxWeight μ i+
--               H*(axialSectionArea (openRepresentative F) i (if a then 1/2 else 0)-V)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.axialFluxWeight`, `OAI.CubicTorus.axialSectionArea`, `OAI.CubicTorus.axialSlicePerimeter`, `OAI.CubicTorus.chamberCorner`, `OAI.CubicTorus.chamberVertex`, `OAI.CubicTorus.coordinateHalf`, `OAI.CubicTorus.coordinateReflection`, `OAI.CubicTorus.directionalFlux`, `OAI.CubicTorus.openRepresentative`, `OAI.CubicTorus.Periodic.Variation` and `OAI.CubicTorus.Periodic.normalFirstVariation` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.SmallStandardRegion`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.latticeVector`, `OAI.CubicTorus.quotientMap` and `OAI.CubicTorus.torusVolume` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI_CubicTorus_isMinimizerAt_cylinder_contact_nonstandard_star`, `OAI.CubicTorus.isMinimizerAt_cylinder_contact_standard`, `OAI.CubicTorus.isMinimizerAt_first_transition_nonstandard_two_vertices` and `OAI.CubicTorus.isMinimizerAt_second_transition_nonstandard_star` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/ChamberPositionProducer.lean (declaration OAI.CubicTorus.isMinimizerAt_nonstandard_section_system)

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

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_nonstandard_section_system {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hmE : IsMinimizerAt V E) (hnstd : ¬SmallStandardRegion V E) :
    ∃ (b : Torus) (F : Set Torus) (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
      (_ : ContDiff ℝ (⊤ : ℕ∞) N) (_ : ∀ m x,N (x+latticeVector m)=N x)
      (s : Fin 3 → Bool) (H : ℝ),
      MeasurableSet F ∧ F =ᵐ[torusVolume] ((fun z => z+b) ⁻¹' E) ∧ IsMinimizerAt V F ∧
      IsPreconnected (frontier (openRepresentative F)) ∧ IsNormalMeasure F μ ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ i : Fin 3,coordinateReflection i ⁻¹' F =ᵐ[torusVolume] F) ∧
      (∀ (x : Cover) (i : Fin 3),
        quotientMap x∈frontier (openRepresentative F)∩coordinateHalf i (if s i then 0 else 1/2) → 0<N x i) ∧
      (∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
        H*directionalFlux F D.coordinate D.function) ∧
      (0<(μ.mass : ℝ)) ∧ (∑ i : Fin 3,axialFluxWeight μ i)=2 ∧
      (∀ i : Fin 3,0≤axialFluxWeight μ i ∧ axialFluxWeight μ i<1) ∧
      (∃ i : Fin 3,quotientMap (chamberVertex s (fun j => decide (j=i)))∈closure (openRepresentative F)) ∧
      (∀ i : Fin 3,Continuous (axialSectionArea (openRepresentative F) i) ∧
        AntitoneOn (axialSectionArea (openRepresentative F) i)
          (Icc (chamberCorner s i) (chamberCorner s i+1/2))) ∧
      (∀ i : Fin 3,
        2*(axialSectionArea (openRepresentative F) i (chamberCorner s i)-
          axialSectionArea (openRepresentative F) i (chamberCorner s i+1/2))≤
          (μ.mass : ℝ)*Real.sqrt (1-axialFluxWeight μ i)) ∧
      (∀ (i : Fin 3) (a : Bool),
        axialSlicePerimeter (openRepresentative F) i (if a then 1/2 else 0)=
          ENNReal.ofReal ((μ.mass : ℝ)*axialFluxWeight μ i+
            H*(axialSectionArea (openRepresentative F) i (if a then 1/2 else 0)-V))) := by
  sorry

end CubicTorus

end
end

end OAI
end
