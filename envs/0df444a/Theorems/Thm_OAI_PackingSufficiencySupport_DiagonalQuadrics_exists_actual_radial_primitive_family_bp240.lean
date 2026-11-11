-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_DiagonalQuadrics_exists_actual_radial_primitive_family_bp240
-- name    : OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_actual_radial_primitive_family_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:52:12.880178+00:00
-- url     : https://prove2.me/theorems/4fe84396-5957-4345-bb36-e620f458cb50
-- title:
--   OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_actual_radial_primitive_family_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_actual_radial_primitive_family` of [lean/OAI/Geometry/BallPacking/Normal/QuadricMovingCone.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Normal/QuadricMovingCone.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.DiagonalQuadrics`, with `open scoped ContDiff Manifold Topology`, `open Set Function Manifold`, `open Hamiltonian`):
--
--   ```lean
--    theorem exists_actual_radial_primitive_family_bp240 {d : ℝ} (hd : 0<d)
--       {K : Set (NormalSpace a)} (hK : IsCompact K)
--       (hKd : ∀ x∈K,phaseSq x.2<d/Real.pi) :
--       ∃ A : ℝ × NormalSpace a → Affine m,∃ Γ : ℝ → ManifoldOneForm (NormalModel m) (NormalSpace a),
--         ∃ ε : ℝ,0<ε ∧ ∃ U : Set (NormalSpace a),IsOpen U ∧ K⊆U ∧
--         ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,NormalModel m)) 𝓘(ℝ,Affine m) ∞ A ∧
--         SmoothOneFormFamily Γ ∧ EqOn (Γ 0) (normalCouplingPrimitive a) U ∧
--         (∀ t∈Ioc (0:ℝ) ε,Topology.IsEmbedding (fun x : U => A (t,x.val))) ∧
--         (∀ t∈Ioc (0:ℝ) ε,∀ x∈U,Γ t x=
--           (normalAmbientPrimitive a (1/Real.pi) d t (A (t,x))).comp
--             (manifoldMapDifferential (E := Affine m) (F := NormalModel m) (fun y => A (t,y)) x))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.DiagonalQuadrics.Affine`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.RealModel`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.locus`, `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.Plane`, `OAI.PackingSufficiencySupport.Hamiltonian.PlanePhase`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothOneFormFamily`, `OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace`, `OAI.PackingSufficiencySupport.Hamiltonian.manifoldMapDifferential` and `OAI.PackingSufficiencySupport.Hamiltonian.phaseSq` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.DiagonalQuadrics.realSurfaceChartedSpace` (definitions bundle `OAIQ240Bp015` of this split); `OAI.PackingSufficiencySupport.DiagonalQuadrics.NormalModel`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.NormalSpace`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.normalAmbientPrimitive` and `OAI.PackingSufficiencySupport.DiagonalQuadrics.normalCouplingPrimitive` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proof of `OAI.PackingSufficiencySupport.actual_complement_packing_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Normal/QuadricMovingCone.lean (declaration OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_actual_radial_primitive_family)

import Mathlib
import Definitions.Def_OAIQ240Bp019

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Hamiltonian

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

 theorem exists_actual_radial_primitive_family_bp240 {d : ℝ} (hd : 0<d)
    {K : Set (NormalSpace a)} (hK : IsCompact K)
    (hKd : ∀ x∈K,phaseSq x.2<d/Real.pi) :
    ∃ A : ℝ × NormalSpace a → Affine m,∃ Γ : ℝ → ManifoldOneForm (NormalModel m) (NormalSpace a),
      ∃ ε : ℝ,0<ε ∧ ∃ U : Set (NormalSpace a),IsOpen U ∧ K⊆U ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,NormalModel m)) 𝓘(ℝ,Affine m) ∞ A ∧
      SmoothOneFormFamily Γ ∧ EqOn (Γ 0) (normalCouplingPrimitive a) U ∧
      (∀ t∈Ioc (0:ℝ) ε,Topology.IsEmbedding (fun x : U => A (t,x.val))) ∧
      (∀ t∈Ioc (0:ℝ) ε,∀ x∈U,Γ t x=
        (normalAmbientPrimitive a (1/Real.pi) d t (A (t,x))).comp
          (manifoldMapDifferential (E := Affine m) (F := NormalModel m) (fun y => A (t,y)) x)) := by
  sorry

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end
