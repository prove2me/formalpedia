-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_MomentPolytope_Annular_exhausted_surface_packing_bp240
-- name    : OAI.PackingSufficiencySupport.MomentPolytope.Annular.exhausted_surface_packing_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:55:36.12256+00:00
-- url     : https://prove2.me/theorems/8bc9a0d9-4f10-407b-8a2a-27729c901ee0
-- title:
--   OAI.PackingSufficiencySupport.MomentPolytope.Annular.exhausted_surface_packing_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.MomentPolytope.Annular.exhausted_surface_packing` of [lean/OAI/Geometry/BallPacking/Models/SurfaceComparison.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Models/SurfaceComparison.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.MomentPolytope.Annular`, with `open scoped ContDiff Manifold Topology BigOperators Pointwise`, `open Set Function Manifold MeasureTheory`, `open Hamiltonian Hamiltonian.AnnularHandleData`):
--
--   ```lean
--    theorem exhausted_surface_packing_bp240 {m q N : ℕ} [Nonempty (Fin N)]
--       (bF : Fin q → Moments m) (cF : Fin q → ℝ)
--       (hbF : ∀ ν j,0≤bF ν j) (hcF : ∀ ν,0 < cF ν) (hcomp : IsCompact (region bF cF))
--       (A : Moments m → ℝ) (hA : ContinuousOn A (region bF cF))
--       (hAp : ∀ p∈region bF cF,0<A p) (r r' : Fin N → ℝ)
--       (hr' : ∀ i,0 ≤ r' i) (hrr : ∀ i,r' i < r i)
--       (hsimplex : ∀ i,∀ p : Moments m,(∀ j,0≤p j) → (∑ j,p j) ≤ r i → p∈region bF cF)
--       (hface : ∀ i,∀ p : Moments m,(∀ j,0≤p j) → (∑ j,p j) ≤ r i →
--         ∀ ν,(∑ j,bF ν j*p j)≠cF ν)
--       (hconc : ConcaveOn ℝ (region bF cF) (fun p => A p-∑ i,max (r i-∑ j,p j) 0))
--       (hmean : 0<∫ p in region bF cF,A p-∑ i,max (r i-∑ j,p j) 0)
--       {τ d₀ : ℝ} (hτ : 0<τ) (hτ1 : τ<1) (hd₀ : 0<d₀)
--       (houter : ∀ p∈region bF cF,p∉τ • region bF cF → d₀≤A p-∑ i,max (r i-∑ j,p j) 0)
--       (Kbase : ℕ → Set M) (hD : ∀ ℓ,IsCompact (Kbase ℓ))
--       (hmono : ∀ ℓ,Kbase ℓ⊆interior (Kbase (ℓ+1))) (hcover : (⋃ ℓ,Kbase ℓ)=univ)
--       (hcD : ∀ ℓ,IsPreconnected (interior (Kbase ℓ))) (hne : ∀ ℓ,(interior (Kbase ℓ)).Nonempty)
--       (hb : ∀ ℓ,HasSmoothSurfaceBoundary (Kbase ℓ)) (hor : PositivePlaneTransitions M)
--       (D : AnnularHandleData Plane M)
--       {b δ : ℝ} (hbp : 0<b) (hbw : b<D.width) (hδ : 0<δ) (hsmall : δ<1/2)
--       (heor : PositivePartialChart D.densityChart)
--       (hclock : D.clock=positiveCircleClock δ)
--       {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
--       (hsΛ : ∀ x u v,Λ x u v= -Λ x v u)
--       (hpΛ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target → 0 < chartTwoForm Λ c y (1,0) (0,1))
--       (d : ℕ → Moments m × M → ℝ)
--       (hd : ∀ ℓ,ContMDiff (𝓘(ℝ,Moments m).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ (d ℓ))
--       (hdp : ∀ ℓ,∀ p∈region bF cF,∀ x∈Kbase ℓ,0<d ℓ (p,x))
--       (Γ : ℕ → Moments m → ManifoldOneForm Plane M) (hΓ : ∀ ℓ,SmoothOneFormFamily (Γ ℓ))
--       (hdΓ : ∀ ℓ p x,manifoldExteriorOneForm (Γ ℓ p) x=d ℓ (p,x) • Λ x)
--       (hlim : TendstoUniformlyOn (fun ℓ p => compactSurfaceFormIntegral (hD ℓ)
--         (fun x => d ℓ (p,x) • Λ x)) A Filter.atTop (region bF cF)) :
--       ∃ ℓ,∃ φ : Fin N → Ambient (m+1) → M × PlanePhase (Fin m),
--         (∀ i,FormNeighborhoodEmbedding (closedBall (m+1) (r' i)) (fun _ => successorStandardForm m)
--           (globalHorizontalCoupling phaseArea (Γ ℓ ∘ planeMoments)) (φ i)) ∧
--         (∀ i,MapsTo (φ i) (closedBall (m+1) (r' i)) (interior (Kbase ℓ ×ˢ planeRegion bF cF))) ∧
--         Pairwise (fun i j => Disjoint (φ i '' closedBall (m+1) (r' i)) (φ j '' closedBall (m+1) (r' j)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.Ambient`, `OAI.PackingSufficiencySupport.Hamiltonian.FormNeighborhoodEmbedding`, `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldTwoForm`, `OAI.PackingSufficiencySupport.Hamiltonian.Plane`, `OAI.PackingSufficiencySupport.Hamiltonian.PlanePhase`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothOneFormFamily`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothTwoForm`, `OAI.PackingSufficiencySupport.Hamiltonian.chartTwoForm`, `OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace`, `OAI.PackingSufficiencySupport.Hamiltonian.manifoldExteriorOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.phaseArea` and `OAI.PackingSufficiencySupport.MomentPolytope.Moments` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.HasSmoothSurfaceBoundary` (definitions bundle `OAIQ240Bp004` of this split); `OAI.PackingSufficiencySupport.closedBall`, `OAI.PackingSufficiencySupport.Hamiltonian.PositivePartialChart`, `OAI.PackingSufficiencySupport.Hamiltonian.PositivePlaneTransitions`, `OAI.PackingSufficiencySupport.Hamiltonian.positiveCircleClock` and `OAI.PackingSufficiencySupport.MomentPolytope.region` (definitions bundle `OAIQ240Bp007` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.compactSurfaceFormIntegral`, `OAI.PackingSufficiencySupport.Hamiltonian.globalHorizontalCoupling` and `OAI.PackingSufficiencySupport.Hamiltonian.planeMoments` (definitions bundle `OAIQ240Bp010` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData` and `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart` (definitions bundle `OAIQ240Bp015` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.successorStandardForm` and `OAI.PackingSufficiencySupport.MomentPolytope.planeRegion` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proofs of `OAI.PackingSufficiencySupport.CubicModel.actual_cubic_representative_packing_bp240`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.actual_large_normal_packing_bp240` and `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.actual_small_normal_packing_bp240` of this split import it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Models/SurfaceComparison.lean (declaration OAI.PackingSufficiencySupport.MomentPolytope.Annular.exhausted_surface_packing)

import Mathlib
import Definitions.Def_OAIQ240Bp019

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.MomentPolytope.Annular
open scoped ContDiff Manifold Topology BigOperators Pointwise
open Set Function Manifold MeasureTheory
open Hamiltonian Hamiltonian.AnnularHandleData

variable {M : Type} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [TopologicalSpace.PseudoMetrizableSpace M] [MeasurableSpace M] [BorelSpace M]

 theorem exhausted_surface_packing_bp240 {m q N : ℕ} [Nonempty (Fin N)]
    (bF : Fin q → Moments m) (cF : Fin q → ℝ)
    (hbF : ∀ ν j,0≤bF ν j) (hcF : ∀ ν,0 < cF ν) (hcomp : IsCompact (region bF cF))
    (A : Moments m → ℝ) (hA : ContinuousOn A (region bF cF))
    (hAp : ∀ p∈region bF cF,0<A p) (r r' : Fin N → ℝ)
    (hr' : ∀ i,0 ≤ r' i) (hrr : ∀ i,r' i < r i)
    (hsimplex : ∀ i,∀ p : Moments m,(∀ j,0≤p j) → (∑ j,p j) ≤ r i → p∈region bF cF)
    (hface : ∀ i,∀ p : Moments m,(∀ j,0≤p j) → (∑ j,p j) ≤ r i →
      ∀ ν,(∑ j,bF ν j*p j)≠cF ν)
    (hconc : ConcaveOn ℝ (region bF cF) (fun p => A p-∑ i,max (r i-∑ j,p j) 0))
    (hmean : 0<∫ p in region bF cF,A p-∑ i,max (r i-∑ j,p j) 0)
    {τ d₀ : ℝ} (hτ : 0<τ) (hτ1 : τ<1) (hd₀ : 0<d₀)
    (houter : ∀ p∈region bF cF,p∉τ • region bF cF → d₀≤A p-∑ i,max (r i-∑ j,p j) 0)
    (Kbase : ℕ → Set M) (hD : ∀ ℓ,IsCompact (Kbase ℓ))
    (hmono : ∀ ℓ,Kbase ℓ⊆interior (Kbase (ℓ+1))) (hcover : (⋃ ℓ,Kbase ℓ)=univ)
    (hcD : ∀ ℓ,IsPreconnected (interior (Kbase ℓ))) (hne : ∀ ℓ,(interior (Kbase ℓ)).Nonempty)
    (hb : ∀ ℓ,HasSmoothSurfaceBoundary (Kbase ℓ)) (hor : PositivePlaneTransitions M)
    (D : AnnularHandleData Plane M)
    {b δ : ℝ} (hbp : 0<b) (hbw : b<D.width) (hδ : 0<δ) (hsmall : δ<1/2)
    (heor : PositivePartialChart D.densityChart)
    (hclock : D.clock=positiveCircleClock δ)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hsΛ : ∀ x u v,Λ x u v= -Λ x v u)
    (hpΛ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target → 0 < chartTwoForm Λ c y (1,0) (0,1))
    (d : ℕ → Moments m × M → ℝ)
    (hd : ∀ ℓ,ContMDiff (𝓘(ℝ,Moments m).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ (d ℓ))
    (hdp : ∀ ℓ,∀ p∈region bF cF,∀ x∈Kbase ℓ,0<d ℓ (p,x))
    (Γ : ℕ → Moments m → ManifoldOneForm Plane M) (hΓ : ∀ ℓ,SmoothOneFormFamily (Γ ℓ))
    (hdΓ : ∀ ℓ p x,manifoldExteriorOneForm (Γ ℓ p) x=d ℓ (p,x) • Λ x)
    (hlim : TendstoUniformlyOn (fun ℓ p => compactSurfaceFormIntegral (hD ℓ)
      (fun x => d ℓ (p,x) • Λ x)) A Filter.atTop (region bF cF)) :
    ∃ ℓ,∃ φ : Fin N → Ambient (m+1) → M × PlanePhase (Fin m),
      (∀ i,FormNeighborhoodEmbedding (closedBall (m+1) (r' i)) (fun _ => successorStandardForm m)
        (globalHorizontalCoupling phaseArea (Γ ℓ ∘ planeMoments)) (φ i)) ∧
      (∀ i,MapsTo (φ i) (closedBall (m+1) (r' i)) (interior (Kbase ℓ ×ˢ planeRegion bF cF))) ∧
      Pairwise (fun i j => Disjoint (φ i '' closedBall (m+1) (r' i)) (φ j '' closedBall (m+1) (r' j))) := by
  sorry

end PackingSufficiencySupport.MomentPolytope.Annular

end

end OAI
end
