-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_AnnularHandleData_exists_surface_normal_form_packing_bp240
-- name    : OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.exists_surface_normal_form_packing_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:56:28.759336+00:00
-- url     : https://prove2.me/theorems/131cab57-0935-4587-9a83-d2bf429bedc6
-- title:
--   OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.exists_surface_normal_form_packing_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.exists_surface_normal_form_packing` of [lean/OAI/Geometry/BallPacking/Hamiltonian/AnnularDensityMass.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Hamiltonian/AnnularDensityMass.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData`, with `open scoped ContDiff Manifold Topology`, `open Set Function Manifold MeasureTheory`, `open scoped BigOperators`):
--
--   ```lean
--    theorem exists_surface_normal_form_packing_bp240 {m N : ℕ}
--       (D : AnnularHandleData Plane M)
--       {b δ : ℝ} (hb : 0<b) (hbw : b<D.width) (hδ : 0<δ) (hsmall : δ<1/2)
--       (hor : PositivePartialChart D.densityChart)
--       (hclock : D.clock=positiveCircleClock δ)
--       {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
--       (hsΛ : ∀ x u v,Λ x u v= -Λ x v u)
--       (hpΛ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target → 0 < chartTwoForm Λ c y (1,0) (0,1))
--       {γ : ManifoldOneForm Plane M} {ε : ℝ} (hε : 0<ε)
--       (hγ : ∀ x∈D.chart.target,ContDiffAt ℝ ∞
--         (chartOneForm γ x) (extChartAt 𝓘(ℝ,Plane) x x))
--       (hdγ : ∀ x∈D.chart.target,manifoldExteriorOneForm γ x=ε • Λ x)
--       {Γ : (Fin m  →  ℝ)  →  ManifoldOneForm Plane M} (hΓ : SmoothOneFormFamily Γ)
--       {K H : (Fin m  →  ℝ)  →  ℝ} (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H)
--       {Y V : Set (Fin m  →  ℝ)} (hHp : ∀ p∈Y,0≤H p)
--       {Kbase : Set M} (heD : D.chart.target⊆interior Kbase) (hβD : tsupport D.dual⊆interior Kbase)
--       (hΓpos : ∀ p∈Y,∀ x∈Kbase,0 < chartTwoForm (manifoldExteriorOneForm (Γ p)) x
--         (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1))
--       {W : Set M} (hW : IsOpen W) (hBW : D.chart '' band b⊆W)
--       (hWA : W⊆D.chart.target)
--       (hN : ∀ p x,x∈W → Γ p x=γ x+
--         (intervalClock (-b) b (D.chart.symm x).1*H p) • D.dual x)
--       (Φ : CompactHamiltonianIsotopy (phaseArea (ι := Fin m)))
--       (hV : IsOpen (planeMoments ⁻¹' V)) (hVY : V⊆Y)
--       (hΦ : ∀ t∈Icc (0:ℝ) 1,MapsTo (Φ.map t) (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y) ∧
--         MapsTo (Φ.map t).symm (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y))
--       (h : Fin N  →  (Fin m  →  ℝ)  →  ℝ) (hh : ∀ i,ContDiff ℝ ∞ (h i))
--       (hhp : ∀ i p,p∈Y → 0≤h i p)
--       (hres : ∀ v,planeMoments v∈Y → 0 ≤ surfaceRemainder (K ∘ planeMoments) (H ∘ planeMoments)
--         (fun j => h j ∘ planeMoments) (Φ.map 1).symm v)
--       (r r' : Fin N  →  ℝ) (hr' : ∀ i,0 ≤ r' i) (hrr : ∀ i,r' i < r i)
--       (hsimplex : ∀ i,∀ p : Fin m  →  ℝ,(∀ j,0≤p j) → (∑ j,p j) ≤ r' i → p∈V)
--       (hheight : ∀ i,∀ p : Fin m  →  ℝ,(∀ j,0≤p j) → p∈V → r i-(∑ j,p j)≤h i p)
--       {J : Type*} (F : J  →  (Fin m  →  ℝ)  →  ℝ) (hF : ∀ j,ContDiff ℝ ∞ (F j))
--       (α c : J  →  ℝ) (hαc : ∀ j,α j < c j)
--       (hYeq : planeMoments ⁻¹' Y={v | ∀ j,(F j ∘ planeMoments) v ≤ c j})
--       (hYC : IsCompact (planeMoments ⁻¹' Y))
--       (hzero : ∀ j t v,α j<(F j ∘ planeMoments) v →
--         fderiv ℝ (F j ∘ planeMoments) v (hamiltonianField phaseArea Φ.hamiltonian (t,v))=0) :
--       ∃ φ : Fin N  →  Ambient (m+1)  →  M × PlanePhase (Fin m),
--         (∀ i,FormNeighborhoodEmbedding (closedBall (m+1) (r' i)) (fun _ => successorStandardForm m)
--           (globalHorizontalCoupling phaseArea (Γ ∘ planeMoments)) (φ i)) ∧
--         (∀ i,MapsTo (φ i) (closedBall (m+1) (r' i)) (interior (Kbase ×ˢ (planeMoments ⁻¹' Y)))) ∧
--         Pairwise (fun i j => Disjoint (φ i '' closedBall (m+1) (r' i)) (φ j '' closedBall (m+1) (r' j)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.Ambient`, `OAI.PackingSufficiencySupport.Hamiltonian.CircleModel`, `OAI.PackingSufficiencySupport.Hamiltonian.CompactHamiltonianIsotopy`, `OAI.PackingSufficiencySupport.Hamiltonian.CylinderModel`, `OAI.PackingSufficiencySupport.Hamiltonian.FormNeighborhoodEmbedding`, `OAI.PackingSufficiencySupport.Hamiltonian.HandleCylinder`, `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldTwoForm`, `OAI.PackingSufficiencySupport.Hamiltonian.Plane`, `OAI.PackingSufficiencySupport.Hamiltonian.PlanePhase`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothOneFormFamily`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothTwoForm`, `OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.chartTwoForm`, `OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace`, `OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace`, `OAI.PackingSufficiencySupport.Hamiltonian.hamiltonianField`, `OAI.PackingSufficiencySupport.Hamiltonian.intervalClock`, `OAI.PackingSufficiencySupport.Hamiltonian.manifoldExteriorOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.phaseArea` and `OAI.PackingSufficiencySupport.Hamiltonian.surfaceRemainder` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.closedBall`, `OAI.PackingSufficiencySupport.Hamiltonian.PositivePartialChart` and `OAI.PackingSufficiencySupport.Hamiltonian.positiveCircleClock` (definitions bundle `OAIQ240Bp007` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.globalHorizontalCoupling` and `OAI.PackingSufficiencySupport.Hamiltonian.planeMoments` (definitions bundle `OAIQ240Bp010` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData` and `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart` (definitions bundle `OAIQ240Bp015` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.successorStandardForm` and `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.band` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proof of `OAI.PackingSufficiencySupport.MomentPolytope.Annular.exhausted_surface_packing_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Hamiltonian/AnnularDensityMass.lean (declaration OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.exists_surface_normal_form_packing)

import Mathlib
import Definitions.Def_OAIQ240Bp019

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
open scoped BigOperators

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]

 theorem exists_surface_normal_form_packing_bp240 {m N : ℕ}
    (D : AnnularHandleData Plane M)
    {b δ : ℝ} (hb : 0<b) (hbw : b<D.width) (hδ : 0<δ) (hsmall : δ<1/2)
    (hor : PositivePartialChart D.densityChart)
    (hclock : D.clock=positiveCircleClock δ)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hsΛ : ∀ x u v,Λ x u v= -Λ x v u)
    (hpΛ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target → 0 < chartTwoForm Λ c y (1,0) (0,1))
    {γ : ManifoldOneForm Plane M} {ε : ℝ} (hε : 0<ε)
    (hγ : ∀ x∈D.chart.target,ContDiffAt ℝ ∞
      (chartOneForm γ x) (extChartAt 𝓘(ℝ,Plane) x x))
    (hdγ : ∀ x∈D.chart.target,manifoldExteriorOneForm γ x=ε • Λ x)
    {Γ : (Fin m  →  ℝ)  →  ManifoldOneForm Plane M} (hΓ : SmoothOneFormFamily Γ)
    {K H : (Fin m  →  ℝ)  →  ℝ} (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H)
    {Y V : Set (Fin m  →  ℝ)} (hHp : ∀ p∈Y,0≤H p)
    {Kbase : Set M} (heD : D.chart.target⊆interior Kbase) (hβD : tsupport D.dual⊆interior Kbase)
    (hΓpos : ∀ p∈Y,∀ x∈Kbase,0 < chartTwoForm (manifoldExteriorOneForm (Γ p)) x
      (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1))
    {W : Set M} (hW : IsOpen W) (hBW : D.chart '' band b⊆W)
    (hWA : W⊆D.chart.target)
    (hN : ∀ p x,x∈W → Γ p x=γ x+
      (intervalClock (-b) b (D.chart.symm x).1*H p) • D.dual x)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := Fin m)))
    (hV : IsOpen (planeMoments ⁻¹' V)) (hVY : V⊆Y)
    (hΦ : ∀ t∈Icc (0:ℝ) 1,MapsTo (Φ.map t) (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y) ∧
      MapsTo (Φ.map t).symm (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y))
    (h : Fin N  →  (Fin m  →  ℝ)  →  ℝ) (hh : ∀ i,ContDiff ℝ ∞ (h i))
    (hhp : ∀ i p,p∈Y → 0≤h i p)
    (hres : ∀ v,planeMoments v∈Y → 0 ≤ surfaceRemainder (K ∘ planeMoments) (H ∘ planeMoments)
      (fun j => h j ∘ planeMoments) (Φ.map 1).symm v)
    (r r' : Fin N  →  ℝ) (hr' : ∀ i,0 ≤ r' i) (hrr : ∀ i,r' i < r i)
    (hsimplex : ∀ i,∀ p : Fin m  →  ℝ,(∀ j,0≤p j) → (∑ j,p j) ≤ r' i → p∈V)
    (hheight : ∀ i,∀ p : Fin m  →  ℝ,(∀ j,0≤p j) → p∈V → r i-(∑ j,p j)≤h i p)
    {J : Type*} (F : J  →  (Fin m  →  ℝ)  →  ℝ) (hF : ∀ j,ContDiff ℝ ∞ (F j))
    (α c : J  →  ℝ) (hαc : ∀ j,α j < c j)
    (hYeq : planeMoments ⁻¹' Y={v | ∀ j,(F j ∘ planeMoments) v ≤ c j})
    (hYC : IsCompact (planeMoments ⁻¹' Y))
    (hzero : ∀ j t v,α j<(F j ∘ planeMoments) v →
      fderiv ℝ (F j ∘ planeMoments) v (hamiltonianField phaseArea Φ.hamiltonian (t,v))=0) :
    ∃ φ : Fin N  →  Ambient (m+1)  →  M × PlanePhase (Fin m),
      (∀ i,FormNeighborhoodEmbedding (closedBall (m+1) (r' i)) (fun _ => successorStandardForm m)
        (globalHorizontalCoupling phaseArea (Γ ∘ planeMoments)) (φ i)) ∧
      (∀ i,MapsTo (φ i) (closedBall (m+1) (r' i)) (interior (Kbase ×ˢ (planeMoments ⁻¹' Y)))) ∧
      Pairwise (fun i j => Disjoint (φ i '' closedBall (m+1) (r' i)) (φ j '' closedBall (m+1) (r' j))) := by
  sorry

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

end

end OAI
end
