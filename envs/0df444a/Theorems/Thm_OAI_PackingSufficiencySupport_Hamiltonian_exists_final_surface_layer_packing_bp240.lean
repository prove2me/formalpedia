-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_exists_final_surface_layer_packing_bp240
-- name    : OAI.PackingSufficiencySupport.Hamiltonian.exists_final_surface_layer_packing_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:52:28.109176+00:00
-- url     : https://prove2.me/theorems/80c99262-edba-4cfe-b16a-c9f4dab689ce
-- title:
--   OAI.PackingSufficiencySupport.Hamiltonian.exists_final_surface_layer_packing_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.Hamiltonian.exists_final_surface_layer_packing` of [lean/OAI/Geometry/BallPacking/Layers/ConstructedSurfaceLayers.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Layers/ConstructedSurfaceLayers.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.Hamiltonian`, with `open scoped ContDiff Topology BigOperators`, `open Set Function`):
--
--   ```lean
--   theorem exists_final_surface_layer_packing_bp240 {m N : ℕ}
--       {δ α β : ℝ} (hδ : 0<δ) (hsmall : δ<1/2) (hαβ : α<β)
--       {A B : Plane → ℝ}
--       (hA : ContDiffOn ℝ ∞ A (Ioo α β ×ˢ Ioo (1/2-δ) (1/2+δ)))
--       (hB : ContDiffOn ℝ ∞ B (Ioo α β ×ˢ Ioo (1/2-δ) (1/2+δ)))
--       (hbase : ∀ q∈Ioo α β ×ˢ Ioo (1/2-δ) (1/2+δ),0<fderiv ℝ B q (1,0)-fderiv ℝ A q (0,1))
--       (J : (Fin m → ℝ) → ℝ) (R : PlanePhase (Fin m) → ℝ) (H : Fin N → (Fin m → ℝ) → ℝ)
--       (hJ : ContDiff ℝ ∞ J) (hR : ContDiff ℝ ∞ R) (hH : ∀ i,ContDiff ℝ ∞ (H i))
--       {V : Set (Fin m → ℝ)} (hV : IsOpen (planeMoments ⁻¹' V)) (hHp : ∀ i p,p∈V → 0≤H i p)
--       (r r' : Fin N → ℝ) (hr' : ∀ i,0 ≤ r' i) (hrr : ∀ i,r' i < r i)
--       (hsimplex : ∀ i,∀ p : Fin m → ℝ,(∀ j,0≤p j) → (∑ j,p j) ≤ r' i → p∈V)
--       (hheight : ∀ i,∀ p : Fin m → ℝ,(∀ j,0≤p j) → p∈V → r i - (∑ j,p j) ≤ H i p) :
--       ∃ lo hi : Fin (N+1) → ℝ, ∃ ρ : Fin (N+1) → ℝ → ℝ,
--         (∀ i,α<lo i ∧ lo i<hi i ∧ hi i<β) ∧
--         (∀ i j,i<j → hi i<lo j) ∧
--         (∀ i,ContDiff ℝ ∞ (ρ i) ∧ Monotone (ρ i)) ∧
--         (∀ i s,0≤ρ i s ∧ ρ i s≤1 ∧ 0≤deriv (ρ i) s) ∧
--         (∀ i, ∃ ε : ℝ, 0 < ε ∧ (∀ s, s ≤ lo i + ε → ρ i s = 0) ∧ (∀ s, hi i - ε ≤ s → ρ i s = 1)) ∧
--         ∃ (U : Fin N → Set (Ambient (m+1))) (φ : Fin N → Ambient (m+1) → Plane × PlanePhase (Fin m)),
--           (∀ i,IsOpen (U i)) ∧ (∀ i,closedBall (m+1) (r' i)⊆U i) ∧
--           (∀ i,ContDiffOn ℝ ∞ (φ i) (U i)) ∧
--           (∀ i,Topology.IsEmbedding (fun z : U i => φ i z)) ∧
--           (∀ i,∀ z∈U i,φ i z∈(Ioo (lo i.castSucc) (hi i.castSucc) ×ˢ Ioo (1/2-δ) (1/2+δ)) ×ˢ
--             (planeMoments ⁻¹' V)) ∧
--           (∀ i,∀ z∈U i,∀ v u,
--             horizontalCoupling phaseArea (baseCoefficient A)
--               (weightedSecondCoefficient B (fun q => positiveCircleClock δ (circleTurn q.2))
--                 (surfaceFinalLayer (J ∘ planeMoments) (fun j => H j ∘ planeMoments) R
--                   (fun j => ρ j.castSucc) (ρ (Fin.last N))))
--               (φ i z) (fderiv ℝ (φ i) z v) (fderiv ℝ (φ i) z u)=standardForm v u) ∧
--           Pairwise (fun i j => Disjoint (φ i '' closedBall (m+1) (r' i))
--             (φ j '' closedBall (m+1) (r' j)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.Ambient`, `OAI.PackingSufficiencySupport.Hamiltonian.Plane`, `OAI.PackingSufficiencySupport.Hamiltonian.PlanePhase`, `OAI.PackingSufficiencySupport.Hamiltonian.circleTurn`, `OAI.PackingSufficiencySupport.Hamiltonian.phaseArea` and `OAI.PackingSufficiencySupport.Hamiltonian.surfaceFinalLayer` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.closedBall`, `OAI.PackingSufficiencySupport.standardForm` and `OAI.PackingSufficiencySupport.Hamiltonian.positiveCircleClock` (definitions bundle `OAIQ240Bp007` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.baseCoefficient`, `OAI.PackingSufficiencySupport.Hamiltonian.horizontalCoupling`, `OAI.PackingSufficiencySupport.Hamiltonian.planeMoments` and `OAI.PackingSufficiencySupport.Hamiltonian.weightedSecondCoefficient` (definitions bundle `OAIQ240Bp010` of this split).
--
--   **Used by.** The proof of `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.exists_global_surface_final_packing_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Layers/ConstructedSurfaceLayers.lean (declaration OAI.PackingSufficiencySupport.Hamiltonian.exists_final_surface_layer_packing)

import Mathlib
import Definitions.Def_OAIQ240Bp010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section

open scoped ContDiff Topology BigOperators
open Set Function

theorem exists_final_surface_layer_packing_bp240 {m N : ℕ}
    {δ α β : ℝ} (hδ : 0<δ) (hsmall : δ<1/2) (hαβ : α<β)
    {A B : Plane → ℝ}
    (hA : ContDiffOn ℝ ∞ A (Ioo α β ×ˢ Ioo (1/2-δ) (1/2+δ)))
    (hB : ContDiffOn ℝ ∞ B (Ioo α β ×ˢ Ioo (1/2-δ) (1/2+δ)))
    (hbase : ∀ q∈Ioo α β ×ˢ Ioo (1/2-δ) (1/2+δ),0<fderiv ℝ B q (1,0)-fderiv ℝ A q (0,1))
    (J : (Fin m → ℝ) → ℝ) (R : PlanePhase (Fin m) → ℝ) (H : Fin N → (Fin m → ℝ) → ℝ)
    (hJ : ContDiff ℝ ∞ J) (hR : ContDiff ℝ ∞ R) (hH : ∀ i,ContDiff ℝ ∞ (H i))
    {V : Set (Fin m → ℝ)} (hV : IsOpen (planeMoments ⁻¹' V)) (hHp : ∀ i p,p∈V → 0≤H i p)
    (r r' : Fin N → ℝ) (hr' : ∀ i,0 ≤ r' i) (hrr : ∀ i,r' i < r i)
    (hsimplex : ∀ i,∀ p : Fin m → ℝ,(∀ j,0≤p j) → (∑ j,p j) ≤ r' i → p∈V)
    (hheight : ∀ i,∀ p : Fin m → ℝ,(∀ j,0≤p j) → p∈V → r i - (∑ j,p j) ≤ H i p) :
    ∃ lo hi : Fin (N+1) → ℝ, ∃ ρ : Fin (N+1) → ℝ → ℝ,
      (∀ i,α<lo i ∧ lo i<hi i ∧ hi i<β) ∧
      (∀ i j,i<j → hi i<lo j) ∧
      (∀ i,ContDiff ℝ ∞ (ρ i) ∧ Monotone (ρ i)) ∧
      (∀ i s,0≤ρ i s ∧ ρ i s≤1 ∧ 0≤deriv (ρ i) s) ∧
      (∀ i, ∃ ε : ℝ, 0 < ε ∧ (∀ s, s ≤ lo i + ε → ρ i s = 0) ∧ (∀ s, hi i - ε ≤ s → ρ i s = 1)) ∧
      ∃ (U : Fin N → Set (Ambient (m+1))) (φ : Fin N → Ambient (m+1) → Plane × PlanePhase (Fin m)),
        (∀ i,IsOpen (U i)) ∧ (∀ i,closedBall (m+1) (r' i)⊆U i) ∧
        (∀ i,ContDiffOn ℝ ∞ (φ i) (U i)) ∧
        (∀ i,Topology.IsEmbedding (fun z : U i => φ i z)) ∧
        (∀ i,∀ z∈U i,φ i z∈(Ioo (lo i.castSucc) (hi i.castSucc) ×ˢ Ioo (1/2-δ) (1/2+δ)) ×ˢ
          (planeMoments ⁻¹' V)) ∧
        (∀ i,∀ z∈U i,∀ v u,
          horizontalCoupling phaseArea (baseCoefficient A)
            (weightedSecondCoefficient B (fun q => positiveCircleClock δ (circleTurn q.2))
              (surfaceFinalLayer (J ∘ planeMoments) (fun j => H j ∘ planeMoments) R
                (fun j => ρ j.castSucc) (ρ (Fin.last N))))
            (φ i z) (fderiv ℝ (φ i) z v) (fderiv ℝ (φ i) z u)=standardForm v u) ∧
        Pairwise (fun i j => Disjoint (φ i '' closedBall (m+1) (r' i))
          (φ j '' closedBall (m+1) (r' j))) := by
  sorry

end

open scoped ContDiff
open Set Function

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end
