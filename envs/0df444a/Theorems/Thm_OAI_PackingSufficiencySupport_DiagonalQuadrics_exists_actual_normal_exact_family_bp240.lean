-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_DiagonalQuadrics_exists_actual_normal_exact_family_bp240
-- name    : OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_actual_normal_exact_family_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:54:27.145223+00:00
-- url     : https://prove2.me/theorems/afe589f6-2c4f-44bb-977c-995241f36133
-- title:
--   OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_actual_normal_exact_family_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_actual_normal_exact_family` of [lean/OAI/Geometry/BallPacking/Normal/QuadricMovingCone.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Normal/QuadricMovingCone.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.DiagonalQuadrics`, with `open scoped ContDiff Manifold Topology`, `open Set Function Manifold`, `open Hamiltonian`, `open scoped BigOperators`):
--
--   ```lean
--    theorem exists_actual_normal_exact_family_bp240 {K : Set (locus a)} {H : Set (Fin m → ℂ)}
--       (hK : IsCompact K) (hH : IsCompact H) (c d : ℝ) :
--       ∃ Ψ : ℝ × ConeSpace a → Affine m, ∃ Γ : ℝ → ManifoldOneForm (ConeModel m) (ConeSpace a),
--         ∃ ε : ℝ,0<ε ∧ ∃ U : Set (ConeSpace a),IsOpen U ∧ K×ˢH⊆U ∧
--         ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ConeModel m)) 𝓘(ℝ,Affine m) ∞ Ψ ∧
--         SmoothOneFormFamily Γ ∧ Γ 0=centralConePrimitive a c d ∧
--         (∀ t∈Icc (-ε) ε,t≠0 → Topology.IsEmbedding (fun p : U => Ψ (t,p.val))) ∧
--         (∀ t∈Icc (-ε) ε,t≠0 → ∀ p∈U,
--           manifoldExteriorOneForm (Γ t) p=
--             (normalAmbientForm a c d t (Ψ (t,p))).bilinearComp
--               (manifoldMapDifferential (E := Affine m) (F := ConeModel m) (fun q => Ψ (t,q)) p)
--               (manifoldMapDifferential (E := Affine m) (F := ConeModel m) (fun q => Ψ (t,q)) p))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.DiagonalQuadrics.Affine`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.RealModel`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.locus`, `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothOneFormFamily`, `OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace`, `OAI.PackingSufficiencySupport.Hamiltonian.manifoldExteriorOneForm` and `OAI.PackingSufficiencySupport.Hamiltonian.manifoldMapDifferential` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.DiagonalQuadrics.realSurfaceChartedSpace` (definitions bundle `OAIQ240Bp015` of this split); `OAI.PackingSufficiencySupport.DiagonalQuadrics.ConeModel`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.ConeSpace`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.centralConePrimitive` and `OAI.PackingSufficiencySupport.DiagonalQuadrics.normalAmbientForm` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proof of `OAI.HigherDimensionalBallPacking.main_theorem` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Normal/QuadricMovingCone.lean (declaration OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_actual_normal_exact_family)

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
open scoped BigOperators
section

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

 theorem exists_actual_normal_exact_family_bp240 {K : Set (locus a)} {H : Set (Fin m → ℂ)}
    (hK : IsCompact K) (hH : IsCompact H) (c d : ℝ) :
    ∃ Ψ : ℝ × ConeSpace a → Affine m, ∃ Γ : ℝ → ManifoldOneForm (ConeModel m) (ConeSpace a),
      ∃ ε : ℝ,0<ε ∧ ∃ U : Set (ConeSpace a),IsOpen U ∧ K×ˢH⊆U ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ConeModel m)) 𝓘(ℝ,Affine m) ∞ Ψ ∧
      SmoothOneFormFamily Γ ∧ Γ 0=centralConePrimitive a c d ∧
      (∀ t∈Icc (-ε) ε,t≠0 → Topology.IsEmbedding (fun p : U => Ψ (t,p.val))) ∧
      (∀ t∈Icc (-ε) ε,t≠0 → ∀ p∈U,
        manifoldExteriorOneForm (Γ t) p=
          (normalAmbientForm a c d t (Ψ (t,p))).bilinearComp
            (manifoldMapDifferential (E := Affine m) (F := ConeModel m) (fun q => Ψ (t,q)) p)
            (manifoldMapDifferential (E := Affine m) (F := ConeModel m) (fun q => Ψ (t,q)) p)) := by
  sorry

end

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end
