-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_CubicModel_exists_actual_cubic_exact_family_with_zero_bp240
-- name    : OAI.PackingSufficiencySupport.CubicModel.exists_actual_cubic_exact_family_with_zero_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:40:45.72538+00:00
-- url     : https://prove2.me/theorems/836a4734-e168-49bf-b56e-ce59ecee02b9
-- title:
--   OAI.PackingSufficiencySupport.CubicModel.exists_actual_cubic_exact_family_with_zero_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.CubicModel.exists_actual_cubic_exact_family_with_zero` of [lean/OAI/Geometry/BallPacking/Normal/CubicToricAmbient.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Normal/CubicToricAmbient.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.CubicModel`, with `open scoped ContDiff Manifold Topology BigOperators`, `open Set Function Manifold`, `open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial`):
--
--   ```lean
--    theorem exists_actual_cubic_exact_family_with_zero_bp240 {A B : ℕ} (D S : ℕ) (c : ℝ)
--       {K : Set BaseCurve} {H : Set DiskPair} (hK : IsCompact K) (hH : IsCompact H) :
--       ∃ Φ : ℝ × CubicConeSpace → CubicAmbient,
--         ∃ Γ : ℝ → ManifoldOneForm CubicConeModel CubicConeSpace,
--         ∃ ε : ℝ,0<ε ∧ ∃ U : Set CubicConeSpace,IsOpen U ∧ K×ˢH⊆U ∧
--         ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CubicConeModel)) 𝓘(ℝ,CubicAmbient) ∞ Φ ∧
--         (∀ p,Φ (0,p)=(inclusion p.1,p.2.1)) ∧
--         SmoothOneFormFamily Γ ∧ Γ 0=centralCubicPrimitive (A := A) (B := B) D S c ∧
--         (∀ t∈Icc (-ε) ε,t≠0 → Topology.IsEmbedding (fun p : U => Φ (t,p.val))) ∧
--         ∀ t∈Icc (-ε) ε,t≠0 → ∀ p∈U,
--           manifoldExteriorOneForm (Γ t) p=
--             (cubicAmbientForm (A := A) (B := B) D S c t (Φ (t,p))).bilinearComp
--               (manifoldMapDifferential (E := CubicAmbient) (F := CubicConeModel) (fun q => Φ (t,q)) p)
--               (manifoldMapDifferential (E := CubicAmbient) (F := CubicConeModel) (fun q => Φ (t,q)) p)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.CubicModel.CubicAmbient`, `OAI.PackingSufficiencySupport.CubicModel.PlaneBase`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Affine`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.RealModel`, `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothOneFormFamily`, `OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace`, `OAI.PackingSufficiencySupport.Hamiltonian.manifoldExteriorOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.manifoldMapDifferential`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters_injective`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters_nonzero` and `OAI.PackingSufficiencySupport.FiniteMoment.Radial.DiskPair` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.CubicModel.BaseCurve` (definitions bundle `OAIQ240Bp012` of this split); `OAI.PackingSufficiencySupport.CubicModel.CubicConeModel`, `OAI.PackingSufficiencySupport.CubicModel.CubicConeSpace`, `OAI.PackingSufficiencySupport.CubicModel.centralCubicPrimitive`, `OAI.PackingSufficiencySupport.CubicModel.cubicAmbientForm`, `OAI.PackingSufficiencySupport.CubicModel.inclusion` and `OAI.PackingSufficiencySupport.DiagonalQuadrics.realSurfaceChartedSpace` (definitions bundle `OAIQ240Bp015` of this split).
--
--   **Used by.** The proof of `OAI.PackingSufficiencySupport.CubicModel.exists_actual_cubic_normal_transfer_into_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Normal/CubicToricAmbient.lean (declaration OAI.PackingSufficiencySupport.CubicModel.exists_actual_cubic_exact_family_with_zero)

import Mathlib
import Definitions.Def_OAIQ240Bp015

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 theorem exists_actual_cubic_exact_family_with_zero_bp240 {A B : ℕ} (D S : ℕ) (c : ℝ)
    {K : Set BaseCurve} {H : Set DiskPair} (hK : IsCompact K) (hH : IsCompact H) :
    ∃ Φ : ℝ × CubicConeSpace → CubicAmbient,
      ∃ Γ : ℝ → ManifoldOneForm CubicConeModel CubicConeSpace,
      ∃ ε : ℝ,0<ε ∧ ∃ U : Set CubicConeSpace,IsOpen U ∧ K×ˢH⊆U ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CubicConeModel)) 𝓘(ℝ,CubicAmbient) ∞ Φ ∧
      (∀ p,Φ (0,p)=(inclusion p.1,p.2.1)) ∧
      SmoothOneFormFamily Γ ∧ Γ 0=centralCubicPrimitive (A := A) (B := B) D S c ∧
      (∀ t∈Icc (-ε) ε,t≠0 → Topology.IsEmbedding (fun p : U => Φ (t,p.val))) ∧
      ∀ t∈Icc (-ε) ε,t≠0 → ∀ p∈U,
        manifoldExteriorOneForm (Γ t) p=
          (cubicAmbientForm (A := A) (B := B) D S c t (Φ (t,p))).bilinearComp
            (manifoldMapDifferential (E := CubicAmbient) (F := CubicConeModel) (fun q => Φ (t,q)) p)
            (manifoldMapDifferential (E := CubicAmbient) (F := CubicConeModel) (fun q => Φ (t,q)) p) := by
  sorry

end PackingSufficiencySupport.CubicModel

end

end OAI
end
