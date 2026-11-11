-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_CubicModel_actual_cubic_representative_packing_bp240
-- name    : OAI.PackingSufficiencySupport.CubicModel.actual_cubic_representative_packing_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:44:36.902309+00:00
-- url     : https://prove2.me/theorems/5e1ff6b2-16ca-423d-acbd-3b3dea87363f
-- title:
--   OAI.PackingSufficiencySupport.CubicModel.actual_cubic_representative_packing_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.CubicModel.actual_cubic_representative_packing` of [lean/OAI/Geometry/BallPacking/Models/RationalSlack.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Models/RationalSlack.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.CubicModel`, with `open scoped ContDiff Manifold Topology BigOperators Pointwise`, `open Set Function Filter Manifold MeasureTheory`, `open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment MomentPolytope`):
--
--   ```lean
--   theorem actual_cubic_representative_packing_bp240 {A B D S N q : ℕ} [Nonempty (Fin N)]
--       (hA : 0<A) (hS0 : 0<S) (hAB : A≤B) (hSB : S≤B) (hB : 3*B<D) (hS : 3*S<D)
--       {c L : ℝ} (hc : 0 < c)
--       (bF : Fin q → Moments 2) (cF : Fin q → ℝ)
--       (hbF : ∀ ν j,0≤bF ν j) (hcF : ∀ ν,0 < cF ν) (hcomp : IsCompact (region bF cF))
--       (hPS : MapsTo (physicalParameter L) (region bF cF) (Radial.lowerTrapezoid A B))
--       (r r' : Fin N → ℝ) (hr' : ∀ i,0 ≤ r' i) (hrr : ∀ i,r' i < r i)
--       (hsimplex : ∀ i,∀ p : Moments 2,(∀ j,0≤p j) → (∑ j,p j) ≤ r i → p∈region bF cF)
--       (hface : ∀ i,∀ p : Moments 2,(∀ j,0≤p j) → (∑ j,p j) ≤ r i →
--         ∀ ν,(∑ j,bF ν j*p j)≠cF ν)
--       (hconc : ConcaveOn ℝ (region bF cF) (fun p => physicalArea D S c L p-∑ i,max (r i-∑ j,p j) 0))
--       (hmean : 0<∫ p in region bF cF,physicalArea D S c L p-∑ i,max (r i-∑ j,p j) 0)
--       {τ d₀ : ℝ} (hτ : 0<τ) (hτ1 : τ<1) (hd₀ : 0<d₀)
--       (houter : ∀ p∈region bF cF,p∉τ • region bF cF →
--         d₀≤physicalArea D S c L p-∑ i,max (r i-∑ j,p j) 0) :
--       ∃ ℓ,∃ Γ : Moments 2 → ManifoldOneForm RealModel BaseCurve,
--         SmoothOneFormFamily Γ ∧
--         (∀ᶠ q in 𝓝ˢ (region bF cF ×ˢ cubicExhaustion ℓ),
--           physicalParameter L q.1∈Radial.lowerTrapezoid A B →
--           Γ q.1 q.2=physicalPrimitive (A := A) (B := B) D S c L q.1 q.2) ∧
--         ∃ φ : Fin N → Ambient 3 → BaseCurve × PlanePhase (Fin 2),
--           (∀ i,FormNeighborhoodEmbedding (closedBall 3 (r' i)) (fun _ => successorStandardForm 2)
--             (globalHorizontalCoupling phaseArea (Γ ∘ planeMoments)) (φ i)) ∧
--           (∀ i,MapsTo (φ i) (closedBall 3 (r' i)) (interior (cubicExhaustion ℓ ×ˢ planeRegion bF cF))) ∧
--           Pairwise (fun i j => Disjoint (φ i '' closedBall 3 (r' i)) (φ j '' closedBall 3 (r' j)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.Ambient`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Affine`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.RealModel`, `OAI.PackingSufficiencySupport.Hamiltonian.FormNeighborhoodEmbedding`, `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.Plane`, `OAI.PackingSufficiencySupport.Hamiltonian.PlanePhase`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothOneFormFamily`, `OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace`, `OAI.PackingSufficiencySupport.Hamiltonian.phaseArea`, `OAI.PackingSufficiencySupport.MomentPolytope.Moments`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters_injective`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters_nonzero`, `OAI.PackingSufficiencySupport.FiniteMoment.Radial.Plane` and `OAI.PackingSufficiencySupport.FiniteMoment.Radial.lowerTrapezoid` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.closedBall` and `OAI.PackingSufficiencySupport.MomentPolytope.region` (definitions bundle `OAIQ240Bp007` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.globalHorizontalCoupling` and `OAI.PackingSufficiencySupport.Hamiltonian.planeMoments` (definitions bundle `OAIQ240Bp010` of this split); `OAI.PackingSufficiencySupport.CubicModel.BaseCurve` (definitions bundle `OAIQ240Bp012` of this split); `OAI.PackingSufficiencySupport.CubicModel.cubicExhaustion`, `OAI.PackingSufficiencySupport.CubicModel.physicalArea`, `OAI.PackingSufficiencySupport.CubicModel.physicalParameter`, `OAI.PackingSufficiencySupport.CubicModel.physicalPrimitive` and `OAI.PackingSufficiencySupport.DiagonalQuadrics.realSurfaceChartedSpace` (definitions bundle `OAIQ240Bp015` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.successorStandardForm` and `OAI.PackingSufficiencySupport.MomentPolytope.planeRegion` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proof of `OAI.PackingSufficiencySupport.hasPacking_six_large_normalized_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Models/RationalSlack.lean (declaration OAI.PackingSufficiencySupport.CubicModel.actual_cubic_representative_packing)

import Mathlib
import Definitions.Def_OAIQ240Bp019

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators Pointwise
open Set Function Filter Manifold MeasureTheory
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment MomentPolytope

 local instance instSigmaCompactSpaceElemAffineHAddNatOfNatBaseCurve_1_r7596e4_1 : SigmaCompactSpace BaseCurve := curveSigmaCompact (parameters 0)
theorem actual_cubic_representative_packing_bp240 {A B D S N q : ℕ} [Nonempty (Fin N)]
    (hA : 0<A) (hS0 : 0<S) (hAB : A≤B) (hSB : S≤B) (hB : 3*B<D) (hS : 3*S<D)
    {c L : ℝ} (hc : 0 < c)
    (bF : Fin q → Moments 2) (cF : Fin q → ℝ)
    (hbF : ∀ ν j,0≤bF ν j) (hcF : ∀ ν,0 < cF ν) (hcomp : IsCompact (region bF cF))
    (hPS : MapsTo (physicalParameter L) (region bF cF) (Radial.lowerTrapezoid A B))
    (r r' : Fin N → ℝ) (hr' : ∀ i,0 ≤ r' i) (hrr : ∀ i,r' i < r i)
    (hsimplex : ∀ i,∀ p : Moments 2,(∀ j,0≤p j) → (∑ j,p j) ≤ r i → p∈region bF cF)
    (hface : ∀ i,∀ p : Moments 2,(∀ j,0≤p j) → (∑ j,p j) ≤ r i →
      ∀ ν,(∑ j,bF ν j*p j)≠cF ν)
    (hconc : ConcaveOn ℝ (region bF cF) (fun p => physicalArea D S c L p-∑ i,max (r i-∑ j,p j) 0))
    (hmean : 0<∫ p in region bF cF,physicalArea D S c L p-∑ i,max (r i-∑ j,p j) 0)
    {τ d₀ : ℝ} (hτ : 0<τ) (hτ1 : τ<1) (hd₀ : 0<d₀)
    (houter : ∀ p∈region bF cF,p∉τ • region bF cF →
      d₀≤physicalArea D S c L p-∑ i,max (r i-∑ j,p j) 0) :
    ∃ ℓ,∃ Γ : Moments 2 → ManifoldOneForm RealModel BaseCurve,
      SmoothOneFormFamily Γ ∧
      (∀ᶠ q in 𝓝ˢ (region bF cF ×ˢ cubicExhaustion ℓ),
        physicalParameter L q.1∈Radial.lowerTrapezoid A B →
        Γ q.1 q.2=physicalPrimitive (A := A) (B := B) D S c L q.1 q.2) ∧
      ∃ φ : Fin N → Ambient 3 → BaseCurve × PlanePhase (Fin 2),
        (∀ i,FormNeighborhoodEmbedding (closedBall 3 (r' i)) (fun _ => successorStandardForm 2)
          (globalHorizontalCoupling phaseArea (Γ ∘ planeMoments)) (φ i)) ∧
        (∀ i,MapsTo (φ i) (closedBall 3 (r' i)) (interior (cubicExhaustion ℓ ×ˢ planeRegion bF cF))) ∧
        Pairwise (fun i j => Disjoint (φ i '' closedBall 3 (r' i)) (φ j '' closedBall 3 (r' j))) := by
  sorry

end PackingSufficiencySupport.CubicModel
end

end OAI
end
