-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_exists_uniform_compact_exact_fibre_embedding_central_into_bp240
-- name    : OAI.PackingSufficiencySupport.Hamiltonian.exists_uniform_compact_exact_fibre_embedding_central_into_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:44:05.693427+00:00
-- url     : https://prove2.me/theorems/b8bca299-4ae6-4fed-979e-9778190e8af8
-- title:
--   OAI.PackingSufficiencySupport.Hamiltonian.exists_uniform_compact_exact_fibre_embedding_central_into_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.Hamiltonian.exists_uniform_compact_exact_fibre_embedding_central_into` of [lean/OAI/Geometry/BallPacking/Normal/CompactUniformCentral.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Normal/CompactUniformCentral.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.Hamiltonian`, with `open scoped ContDiff Manifold Topology`, `open Set Function Manifold`):
--
--   ```lean
--    theorem exists_uniform_compact_exact_fibre_embedding_central_into_bp240 {Γ : ℝ → ManifoldOneForm E M}
--       (hΓ : SmoothOneFormFamily Γ) {K : Set M} (hK : IsCompact K)
--       (hinv : ∀ x∈K,(manifoldExteriorOneForm (Γ 0) x).IsInvertible)
--       {U : Set M} (hU : IsOpen U) (hKU : K⊆U)
--       {δ : ℝ} (hδ : 0<δ) {A : ℝ × M → N}
--       (hA : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,F) ∞ A)
--       (hemb : ∀ t∈Ioc (0:ℝ) δ,Topology.IsEmbedding (fun x : U => A (t,x.val)))
--       {T : Set N} (hT : IsOpen T) (hinto : MapsTo (fun x => A (0,x)) K T)
--       (Ω : ℝ → ManifoldTwoForm F N)
--       (hform : ∀ t∈Ioc (0:ℝ) δ,∀ x∈U,
--         manifoldExteriorOneForm (Γ t) x=(Ω t (A (t,x))).bilinearComp
--           (manifoldMapDifferential (E := F) (F := E) (fun y => A (t,y)) x)
--           (manifoldMapDifferential (E := F) (F := E) (fun y => A (t,y)) x)) :
--       ∃ η>0,η≤δ ∧ ∀ t∈Ioc (0:ℝ) η,∃ g : M → N,∃ W : Set M,IsOpen W ∧ K⊆W ∧
--         ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ g ∧ Topology.IsEmbedding (fun x : W => g x.val) ∧
--         MapsTo g W T ∧ ∀ x∈W,∀ v w,Ω t (g x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) g x v)
--           (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) g x w)=manifoldExteriorOneForm (Γ 0) x v w
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldTwoForm`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothOneFormFamily`, `OAI.PackingSufficiencySupport.Hamiltonian.manifoldExteriorOneForm` and `OAI.PackingSufficiencySupport.Hamiltonian.manifoldMapDifferential` (definitions bundle `OAIQ240Bp003` of this split).
--
--   **Used by.** The proofs of `OAI.PackingSufficiencySupport.CubicModel.exists_cubic_bubble_separated_bp240` and `OAI.PackingSufficiencySupport.CubicModel.exists_uniform_cubic_bubble_transfer_bp240` of this split import it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Normal/CompactUniformCentral.lean (declaration OAI.PackingSufficiencySupport.Hamiltonian.exists_uniform_compact_exact_fibre_embedding_central_into)

import Mathlib
import Definitions.Def_OAIQ240Bp003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N]

 theorem exists_uniform_compact_exact_fibre_embedding_central_into_bp240 {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) {K : Set M} (hK : IsCompact K)
    (hinv : ∀ x∈K,(manifoldExteriorOneForm (Γ 0) x).IsInvertible)
    {U : Set M} (hU : IsOpen U) (hKU : K⊆U)
    {δ : ℝ} (hδ : 0<δ) {A : ℝ × M → N}
    (hA : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,F) ∞ A)
    (hemb : ∀ t∈Ioc (0:ℝ) δ,Topology.IsEmbedding (fun x : U => A (t,x.val)))
    {T : Set N} (hT : IsOpen T) (hinto : MapsTo (fun x => A (0,x)) K T)
    (Ω : ℝ → ManifoldTwoForm F N)
    (hform : ∀ t∈Ioc (0:ℝ) δ,∀ x∈U,
      manifoldExteriorOneForm (Γ t) x=(Ω t (A (t,x))).bilinearComp
        (manifoldMapDifferential (E := F) (F := E) (fun y => A (t,y)) x)
        (manifoldMapDifferential (E := F) (F := E) (fun y => A (t,y)) x)) :
    ∃ η>0,η≤δ ∧ ∀ t∈Ioc (0:ℝ) η,∃ g : M → N,∃ W : Set M,IsOpen W ∧ K⊆W ∧
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ g ∧ Topology.IsEmbedding (fun x : W => g x.val) ∧
      MapsTo g W T ∧ ∀ x∈W,∀ v w,Ω t (g x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) g x v)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) g x w)=manifoldExteriorOneForm (Γ 0) x v w := by
  sorry

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end
