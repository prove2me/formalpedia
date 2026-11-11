-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_DiagonalQuadrics_exists_actual_normal_transfer_bp240
-- name    : OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_actual_normal_transfer_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:08:14.844231+00:00
-- url     : https://prove2.me/theorems/878c5867-f562-423a-bf0a-5e074d5e706a
-- title:
--   OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_actual_normal_transfer_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_actual_normal_transfer` of [lean/OAI/Geometry/BallPacking/Packings/ComplementPacking.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Packings/ComplementPacking.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.DiagonalQuadrics`, with `open scoped ContDiff Manifold Topology`, `open Set Function Manifold`, `open Hamiltonian`):
--
--   ```lean
--    theorem exists_actual_normal_transfer_bp240 {d : ℝ} (hd : 0<d) (hdhalf : d<1/2)
--       {K : Set (NormalSpace a)} (hK : IsCompact K)
--       (hKd : ∀ p∈K,phaseSq p.2<d/Real.pi) :
--       ∃ t : ℝ,0<t ∧ ∃ g : NormalSpace a → Affine m,∃ W : Set (NormalSpace a),
--         IsOpen W ∧ K⊆W ∧ ContMDiff 𝓘(ℝ,NormalModel m) 𝓘(ℝ,Affine m) ∞ g ∧
--         Topology.IsEmbedding (fun x : W => g x.val) ∧
--         ∀ x∈W,∀ v w,normalAmbientForm a (1/Real.pi) d t (g x)
--           (manifoldMapDifferential (E := Affine m) (F := NormalModel m) g x v)
--           (manifoldMapDifferential (E := Affine m) (F := NormalModel m) g x w)=
--           globalHorizontalCoupling phaseArea (normalHorizontalPrimitive (q := m) a 2 ∘ planeMoments) x v w
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.DiagonalQuadrics.Affine`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.RealModel`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.locus`, `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.Plane`, `OAI.PackingSufficiencySupport.Hamiltonian.PlanePhase`, `OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace`, `OAI.PackingSufficiencySupport.Hamiltonian.manifoldMapDifferential`, `OAI.PackingSufficiencySupport.Hamiltonian.phaseArea` and `OAI.PackingSufficiencySupport.Hamiltonian.phaseSq` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.globalHorizontalCoupling` and `OAI.PackingSufficiencySupport.Hamiltonian.planeMoments` (definitions bundle `OAIQ240Bp010` of this split); `OAI.PackingSufficiencySupport.DiagonalQuadrics.realSurfaceChartedSpace` (definitions bundle `OAIQ240Bp015` of this split); `OAI.PackingSufficiencySupport.DiagonalQuadrics.NormalModel`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.NormalSpace`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.normalAmbientForm` and `OAI.PackingSufficiencySupport.DiagonalQuadrics.normalHorizontalPrimitive` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proofs of `OAI.HigherDimensionalBallPacking.main_theorem` and `OAI.PackingSufficiencySupport.hasPacking_dim_ge_four_bp240` of this split import it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Packings/ComplementPacking.lean (declaration OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_actual_normal_transfer)

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

 theorem exists_actual_normal_transfer_bp240 {d : ℝ} (hd : 0<d) (hdhalf : d<1/2)
    {K : Set (NormalSpace a)} (hK : IsCompact K)
    (hKd : ∀ p∈K,phaseSq p.2<d/Real.pi) :
    ∃ t : ℝ,0<t ∧ ∃ g : NormalSpace a → Affine m,∃ W : Set (NormalSpace a),
      IsOpen W ∧ K⊆W ∧ ContMDiff 𝓘(ℝ,NormalModel m) 𝓘(ℝ,Affine m) ∞ g ∧
      Topology.IsEmbedding (fun x : W => g x.val) ∧
      ∀ x∈W,∀ v w,normalAmbientForm a (1/Real.pi) d t (g x)
        (manifoldMapDifferential (E := Affine m) (F := NormalModel m) g x v)
        (manifoldMapDifferential (E := Affine m) (F := NormalModel m) g x w)=
        globalHorizontalCoupling phaseArea (normalHorizontalPrimitive (q := m) a 2 ∘ planeMoments) x v w := by
  sorry

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end
