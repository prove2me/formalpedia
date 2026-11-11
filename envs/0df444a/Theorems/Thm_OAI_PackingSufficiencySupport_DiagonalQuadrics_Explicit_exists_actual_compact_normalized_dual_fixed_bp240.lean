-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_DiagonalQuadrics_Explicit_exists_actual_compact_normalized_dual_fixed_bp240
-- name    : OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.exists_actual_compact_normalized_dual_fixed_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:51:25.035914+00:00
-- url     : https://prove2.me/theorems/122b2b58-c9d4-46dc-a388-c01d819bed9d
-- title:
--   OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.exists_actual_compact_normalized_dual_fixed_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.exists_actual_compact_normalized_dual_fixed` of [lean/OAI/Geometry/BallPacking/Annuli/AnnularChartNormalization.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Annuli/AnnularChartNormalization.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit`, with `open scoped ContDiff Manifold Topology`, `open Set Function Manifold MeasureTheory`, `open Hamiltonian`):
--
--   ```lean
--   theorem exists_actual_compact_normalized_dual_fixed_bp240
--       {f : Circle → ℝ} (hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f)
--       (hfi : (∫ t in (0:ℝ)..1,f (circleTurn t))=1) :
--       ∃ (a : ℝ) (e : PartialDiffeomorph 𝓘(ℝ,CylinderModel) 𝓘(ℝ,RealModel)
--         HandleCylinder (Surface m) ∞) (β : ManifoldOneForm RealModel (Surface m)),
--         a=transverseCylinderWidth m/2 ∧
--         e=restrictedTransverseCylinder m (transverseCylinderWidth m/2) ∧
--         0<a ∧ e.source=Ioo (-a) a ×ˢ univ ∧ IsCompact (closure e.target) ∧
--         SmoothOneFormFamily (fun _ : ℝ => β) ∧ HasCompactSupport β ∧
--         (∀ x,manifoldExteriorOneForm β x=0) ∧
--         ∀ z∈e.source,∀ v : CylinderModel,
--           β (e z) (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,RealModel) e z v)=
--             f z.2*circleAngular z.2 v.2
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.DiagonalQuadrics.Affine`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.RealModel`, `OAI.PackingSufficiencySupport.Hamiltonian.CircleModel`, `OAI.PackingSufficiencySupport.Hamiltonian.CylinderModel`, `OAI.PackingSufficiencySupport.Hamiltonian.HandleCylinder`, `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothOneFormFamily`, `OAI.PackingSufficiencySupport.Hamiltonian.circleTurn`, `OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace`, `OAI.PackingSufficiencySupport.Hamiltonian.manifoldExteriorOneForm`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters_injective` and `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters_nonzero` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.Surface` (definitions bundle `OAIQ240Bp009` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.circleAngular` (definitions bundle `OAIQ240Bp010` of this split); `OAI.PackingSufficiencySupport.DiagonalQuadrics.realSurfaceChartedSpace` (definitions bundle `OAIQ240Bp015` of this split); `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.restrictedTransverseCylinder` and `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinderWidth` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proofs of `OAI.PackingSufficiencySupport.CubicModel.actual_cubic_representative_packing_bp240`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.actual_large_normal_packing_bp240` and `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.actual_small_normal_packing_bp240` of this split import it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Annuli/AnnularChartNormalization.lean (declaration OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.exists_actual_compact_normalized_dual_fixed)

import Mathlib
import Definitions.Def_OAIQ240Bp019

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
open Hamiltonian

variable (m : ℕ)

theorem exists_actual_compact_normalized_dual_fixed_bp240
    {f : Circle → ℝ} (hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f)
    (hfi : (∫ t in (0:ℝ)..1,f (circleTurn t))=1) :
    ∃ (a : ℝ) (e : PartialDiffeomorph 𝓘(ℝ,CylinderModel) 𝓘(ℝ,RealModel)
      HandleCylinder (Surface m) ∞) (β : ManifoldOneForm RealModel (Surface m)),
      a=transverseCylinderWidth m/2 ∧
      e=restrictedTransverseCylinder m (transverseCylinderWidth m/2) ∧
      0<a ∧ e.source=Ioo (-a) a ×ˢ univ ∧ IsCompact (closure e.target) ∧
      SmoothOneFormFamily (fun _ : ℝ => β) ∧ HasCompactSupport β ∧
      (∀ x,manifoldExteriorOneForm β x=0) ∧
      ∀ z∈e.source,∀ v : CylinderModel,
        β (e z) (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,RealModel) e z v)=
          f z.2*circleAngular z.2 v.2 := by
  sorry

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

end

end OAI
end
