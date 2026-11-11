-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_CubicModel_exists_actual_cubic_normal_transfer_into_bp240
-- name    : OAI.PackingSufficiencySupport.CubicModel.exists_actual_cubic_normal_transfer_into_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:42:43.916008+00:00
-- url     : https://prove2.me/theorems/26eb7c37-3a92-4e48-afdf-981cddebd4e3
-- title:
--   OAI.PackingSufficiencySupport.CubicModel.exists_actual_cubic_normal_transfer_into_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.CubicModel.exists_actual_cubic_normal_transfer_into` of [lean/OAI/Geometry/BallPacking/Normal/CompactDegenerationTransfer.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Normal/CompactDegenerationTransfer.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.CubicModel`, with `open scoped ContDiff Manifold Topology`, `open Set Function Filter Manifold`, `open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial`):
--
--   ```lean
--    theorem exists_actual_cubic_normal_transfer_into_bp240 {A B : ℕ} (hA : 0<A) (hAB : A≤B)
--       (D S : ℕ) {L : ℝ} (hL : 0<L) {K : Set CubicPhysicalSpace} (hK : IsCompact K)
--       (hKd : ∀ p∈K,physicalParameter L (planeMoments p.2)∈lowerTrapezoid A B)
--       (hinv : ∀ p∈K,(cubicPhysicalForm (A := A) (B := B) D S L p).IsInvertible)
--       {T : Set CubicAmbient} (hT : IsOpen T)
--       (hbase : ∀ x : BaseCurve,∀ z : ℂ,(inclusion x,z)∈T) :
--       ∃ t : ℝ,0<t ∧ ∃ g : CubicPhysicalSpace → CubicAmbient,∃ W : Set CubicPhysicalSpace,
--         IsOpen W ∧ K⊆W ∧ ContMDiff 𝓘(ℝ,CubicPhysicalModel) 𝓘(ℝ,CubicAmbient) ∞ g ∧
--         Topology.IsEmbedding (fun x : W => g x.val) ∧ MapsTo g W T ∧
--         ∀ x∈W,∀ v w,cubicAmbientForm (A := A) (B := B) D S (1/(L*Real.pi)) t (g x)
--           (manifoldMapDifferential (E := CubicAmbient) (F := CubicPhysicalModel) g x v)
--           (manifoldMapDifferential (E := CubicAmbient) (F := CubicPhysicalModel) g x w)=
--           cubicPhysicalForm (A := A) (B := B) D S L x v w
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.CubicModel.CubicAmbient`, `OAI.PackingSufficiencySupport.CubicModel.PlaneBase`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Affine`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.RealModel`, `OAI.PackingSufficiencySupport.Hamiltonian.Plane`, `OAI.PackingSufficiencySupport.Hamiltonian.PlanePhase`, `OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace`, `OAI.PackingSufficiencySupport.Hamiltonian.manifoldMapDifferential`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters_injective`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters_nonzero`, `OAI.PackingSufficiencySupport.FiniteMoment.Radial.Plane` and `OAI.PackingSufficiencySupport.FiniteMoment.Radial.lowerTrapezoid` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.planeMoments` (definitions bundle `OAIQ240Bp010` of this split); `OAI.PackingSufficiencySupport.CubicModel.BaseCurve` (definitions bundle `OAIQ240Bp012` of this split); `OAI.PackingSufficiencySupport.CubicModel.CubicPhysicalModel`, `OAI.PackingSufficiencySupport.CubicModel.CubicPhysicalSpace`, `OAI.PackingSufficiencySupport.CubicModel.cubicAmbientForm`, `OAI.PackingSufficiencySupport.CubicModel.cubicPhysicalForm`, `OAI.PackingSufficiencySupport.CubicModel.inclusion`, `OAI.PackingSufficiencySupport.CubicModel.physicalParameter` and `OAI.PackingSufficiencySupport.DiagonalQuadrics.realSurfaceChartedSpace` (definitions bundle `OAIQ240Bp015` of this split).
--
--   **Used by.** The proof of `OAI.PackingSufficiencySupport.hasPacking_six_large_normalized_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Normal/CompactDegenerationTransfer.lean (declaration OAI.PackingSufficiencySupport.CubicModel.exists_actual_cubic_normal_transfer_into)

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
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 theorem exists_actual_cubic_normal_transfer_into_bp240 {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D S : ℕ) {L : ℝ} (hL : 0<L) {K : Set CubicPhysicalSpace} (hK : IsCompact K)
    (hKd : ∀ p∈K,physicalParameter L (planeMoments p.2)∈lowerTrapezoid A B)
    (hinv : ∀ p∈K,(cubicPhysicalForm (A := A) (B := B) D S L p).IsInvertible)
    {T : Set CubicAmbient} (hT : IsOpen T)
    (hbase : ∀ x : BaseCurve,∀ z : ℂ,(inclusion x,z)∈T) :
    ∃ t : ℝ,0<t ∧ ∃ g : CubicPhysicalSpace → CubicAmbient,∃ W : Set CubicPhysicalSpace,
      IsOpen W ∧ K⊆W ∧ ContMDiff 𝓘(ℝ,CubicPhysicalModel) 𝓘(ℝ,CubicAmbient) ∞ g ∧
      Topology.IsEmbedding (fun x : W => g x.val) ∧ MapsTo g W T ∧
      ∀ x∈W,∀ v w,cubicAmbientForm (A := A) (B := B) D S (1/(L*Real.pi)) t (g x)
        (manifoldMapDifferential (E := CubicAmbient) (F := CubicPhysicalModel) g x v)
        (manifoldMapDifferential (E := CubicAmbient) (F := CubicPhysicalModel) g x w)=
        cubicPhysicalForm (A := A) (B := B) D S L x v w := by
  sorry

end PackingSufficiencySupport.CubicModel

end

end OAI
end
