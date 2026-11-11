-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_exists_surface_area_redistribution_bp240
-- name    : OAI.PackingSufficiencySupport.Hamiltonian.exists_surface_area_redistribution_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:55:45.808999+00:00
-- url     : https://prove2.me/theorems/439d5ed2-f7ce-4752-b996-253889948202
-- title:
--   OAI.PackingSufficiencySupport.Hamiltonian.exists_surface_area_redistribution_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.Hamiltonian.exists_surface_area_redistribution` of [lean/OAI/Geometry/BallPacking/SurfaceArea/SurfaceRedistribution.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/SurfaceArea/SurfaceRedistribution.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.Hamiltonian`, with `open scoped ContDiff Manifold Topology`, `open Set Function Manifold MeasureTheory`):
--
--   ```lean
--   theorem exists_surface_area_redistribution_bp240
--       (hK : IsCompact K) (hc : IsPreconnected (interior K)) (hne : (interior K).Nonempty)
--       (hor : PositivePlaneTransitions M)
--       (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
--       (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
--       (hnull : ∀ i,volume ((extChartAt 𝓘(ℝ,Plane) (B i).center).target ∩
--         (extChartAt 𝓘(ℝ,Plane) (B i).center).symm ⁻¹' frontier K)=0)
--       (hZ : IsClosed Z) (hdis : Disjoint (frontier K) Z)
--       {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
--       (hsΛ : ∀ x u v,Λ x u v= -Λ x v u)
--       (hpΛ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
--         0 < chartTwoForm Λ c y (1,0) (0,1))
--       {a : P × M → ℝ} (ha : ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ a)
--       {Y : Set P} (hY : IsCompact Y) (hapos : ∀ p∈Y,∀ x∈K,0<a (p,x))
--       {χ : ManifoldTwoForm Plane M} (hχ : SmoothTwoForm χ)
--       (hsχ : ∀ x u v,χ x u v= -χ x v u)
--       (hpχ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
--         0 ≤ chartTwoForm χ c y (1,0) (0,1))
--       (hT : IsCompact T) (hTK : T⊆interior K) (hzχ : ∀ x,x∉T→χ x=0)
--       (hmχ : partitionFormMass B ρ χ=1)
--       {A : P → ℝ} {ε : ℝ} (hε : 0<ε)
--       (hA : ∀ p∈Y,2*ε<A p)
--       (herr : ∀ p∈Y,|restrictedPartitionFormMass B ρ K (fun x => a (p,x) • Λ x)-A p|<ε) :
--       ∃ (e : ℝ) (b : P × M → ℝ) (H : P → ℝ) (Ξ : P → ManifoldTwoForm Plane M),
--         0<e ∧ ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ b ∧
--         ContDiff ℝ ∞ H ∧ SmoothTwoFormFamily Ξ ∧
--         (∀ p,H p=restrictedPartitionFormMass B ρ K (fun x => a (p,x) • Λ x)-
--           restrictedPartitionFormMass B ρ K (fun x => b (p,x) • Λ x)) ∧
--         (∀ p∈Y,0<H p ∧ |H p-A p|<2*ε) ∧
--         (∀ p x,x∈K→a (p,x) • Λ x+Ξ p x=b (p,x) • Λ x+H p • χ x) ∧
--         (∀ p∈Y,∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
--           (extChartAt 𝓘(ℝ,Plane) c).symm y∈K→
--           0 < chartTwoForm (fun x => a (p,x) • Λ x+Ξ p x) c y (1,0) (0,1)) ∧
--         (∀ p x,x∈Z→b (p,x)=e) ∧
--         HasInteriorPrimitiveFamily (interior K) Ξ ∧
--         (∀ p∈Y,∀ x∈K,0<b (p,x)) ∧
--         (∀ p∈Y,restrictedPartitionFormMass B ρ K (fun x => b (p,x) • Λ x)<ε) ∧
--         (∃ U : Set M,IsOpen U ∧ frontier K⊆U ∧ ∀ p x,x∈U→b (p,x)=a (p,x))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldTwoForm`, `OAI.PackingSufficiencySupport.Hamiltonian.Plane`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothTwoForm`, `OAI.PackingSufficiencySupport.Hamiltonian.SurfaceCoordinateBox`, `OAI.PackingSufficiencySupport.Hamiltonian.chartTwoForm` and `OAI.PackingSufficiencySupport.Hamiltonian.SurfaceCoordinateBox.carrier` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.PositivePlaneTransitions`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothTwoFormFamily` and `OAI.PackingSufficiencySupport.Hamiltonian.partitionFormMass` (definitions bundle `OAIQ240Bp007` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.restrictedPartitionFormMass` (definitions bundle `OAIQ240Bp010` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.HasInteriorPrimitiveFamily` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proof of `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.exists_surface_step_two_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/SurfaceArea/SurfaceRedistribution.lean (declaration OAI.PackingSufficiencySupport.Hamiltonian.exists_surface_area_redistribution)

import Mathlib
import Definitions.Def_OAIQ240Bp019

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [TopologicalSpace.PseudoMetrizableSpace M] [MeasurableSpace M] [BorelSpace M]
  {I : Type*} [Fintype I] {K T Z : Set M}

theorem exists_surface_area_redistribution_bp240
    (hK : IsCompact K) (hc : IsPreconnected (interior K)) (hne : (interior K).Nonempty)
    (hor : PositivePlaneTransitions M)
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    (hnull : ∀ i,volume ((extChartAt 𝓘(ℝ,Plane) (B i).center).target ∩
      (extChartAt 𝓘(ℝ,Plane) (B i).center).symm ⁻¹' frontier K)=0)
    (hZ : IsClosed Z) (hdis : Disjoint (frontier K) Z)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hsΛ : ∀ x u v,Λ x u v= -Λ x v u)
    (hpΛ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0 < chartTwoForm Λ c y (1,0) (0,1))
    {a : P × M → ℝ} (ha : ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ a)
    {Y : Set P} (hY : IsCompact Y) (hapos : ∀ p∈Y,∀ x∈K,0<a (p,x))
    {χ : ManifoldTwoForm Plane M} (hχ : SmoothTwoForm χ)
    (hsχ : ∀ x u v,χ x u v= -χ x v u)
    (hpχ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0 ≤ chartTwoForm χ c y (1,0) (0,1))
    (hT : IsCompact T) (hTK : T⊆interior K) (hzχ : ∀ x,x∉T→χ x=0)
    (hmχ : partitionFormMass B ρ χ=1)
    {A : P → ℝ} {ε : ℝ} (hε : 0<ε)
    (hA : ∀ p∈Y,2*ε<A p)
    (herr : ∀ p∈Y,|restrictedPartitionFormMass B ρ K (fun x => a (p,x) • Λ x)-A p|<ε) :
    ∃ (e : ℝ) (b : P × M → ℝ) (H : P → ℝ) (Ξ : P → ManifoldTwoForm Plane M),
      0<e ∧ ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ b ∧
      ContDiff ℝ ∞ H ∧ SmoothTwoFormFamily Ξ ∧
      (∀ p,H p=restrictedPartitionFormMass B ρ K (fun x => a (p,x) • Λ x)-
        restrictedPartitionFormMass B ρ K (fun x => b (p,x) • Λ x)) ∧
      (∀ p∈Y,0<H p ∧ |H p-A p|<2*ε) ∧
      (∀ p x,x∈K→a (p,x) • Λ x+Ξ p x=b (p,x) • Λ x+H p • χ x) ∧
      (∀ p∈Y,∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
        (extChartAt 𝓘(ℝ,Plane) c).symm y∈K→
        0 < chartTwoForm (fun x => a (p,x) • Λ x+Ξ p x) c y (1,0) (0,1)) ∧
      (∀ p x,x∈Z→b (p,x)=e) ∧
      HasInteriorPrimitiveFamily (interior K) Ξ ∧
      (∀ p∈Y,∀ x∈K,0<b (p,x)) ∧
      (∀ p∈Y,restrictedPartitionFormMass B ρ K (fun x => b (p,x) • Λ x)<ε) ∧
      (∃ U : Set M,IsOpen U ∧ frontier K⊆U ∧ ∀ p x,x∈U→b (p,x)=a (p,x)) := by
  sorry

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end
