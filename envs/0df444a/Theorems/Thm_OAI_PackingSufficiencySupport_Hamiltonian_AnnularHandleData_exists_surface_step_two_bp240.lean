-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_AnnularHandleData_exists_surface_step_two_bp240
-- name    : OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.exists_surface_step_two_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:54:29.582198+00:00
-- url     : https://prove2.me/theorems/f1716f6d-94d3-4fe1-8a26-a653740a251a
-- title:
--   OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.exists_surface_step_two_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.exists_surface_step_two` of [lean/OAI/Geometry/BallPacking/Hamiltonian/AnnularDensityMass.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Hamiltonian/AnnularDensityMass.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData`, with `open scoped ContDiff Manifold Topology`, `open Set Function Manifold MeasureTheory`, `open scoped BigOperators`):
--
--   ```lean
--   theorem exists_surface_step_two_bp240
--       (hK : IsCompact K) (hc : IsPreconnected (interior K)) (hne : (interior K).Nonempty)
--       (hor : PositivePlaneTransitions M)
--       (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
--       (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
--       (hnull : ∀ i,volume ((extChartAt 𝓘(ℝ,Plane) (B i).center).target ∩
--         (extChartAt 𝓘(ℝ,Plane) (B i).center).symm ⁻¹' frontier K)=0)
--       (D : AnnularHandleData Plane M) {b : ℝ} (hb : 0<b) (hbw : b<D.width)
--       (heK : closure D.chart.target⊆interior K) (hβK : tsupport D.dual⊆interior K)
--       (heor : PositivePartialChart D.densityChart)
--       {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
--       (hsΛ : ∀ x u v,Λ x u v= -Λ x v u)
--       (hpΛ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
--         0 < chartTwoForm Λ c y (1,0) (0,1))
--       {c : P × M → ℝ} (hs : ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ c)
--       {Y : Set P} (hY : IsCompact Y) (hcp : ∀ p∈Y,∀ x∈K,0 < c (p,x))
--       {Γ₀ : P → ManifoldOneForm Plane M} (hΓ₀ : SmoothOneFormFamily Γ₀)
--       (hdΓ₀ : ∀ p x,manifoldExteriorOneForm (Γ₀ p) x=c (p,x) • Λ x)
--       {A : P → ℝ} {ε : ℝ} (hε : 0<ε) (hA : ∀ p∈Y,2*ε<A p)
--       (herr : ∀ p∈Y,|restrictedPartitionFormMass B ρ K (fun x => c (p,x) • Λ x)-A p|<ε) :
--       ∃ (q : ℝ) (s : P × M → ℝ) (H : P → ℝ)
--         (Γ₁ : P → ManifoldOneForm Plane M) (γ : ManifoldOneForm Plane M) (L W : Set M),
--         0<q ∧ ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ s ∧ ContDiff ℝ ∞ H ∧
--         (∀ p,H p=restrictedPartitionFormMass B ρ K (fun x => c (p,x) • Λ x)-
--           restrictedPartitionFormMass B ρ K (fun x => s (p,x) • Λ x)) ∧
--         (∀ p∈Y,0<H p ∧ |H p-A p|<2*ε) ∧
--         SmoothOneFormFamily Γ₁ ∧ IsCompact L ∧ L⊆interior K ∧ IsOpen W ∧
--         D.chart '' band b⊆W ∧ W⊆D.chart.target ∧
--         (∀ p x,x∉L→Γ₁ p x=Γ₀ p x) ∧
--         (∀ p x,x∈K→manifoldExteriorOneForm (Γ₁ p) x=
--           s (p,x) • Λ x+H p • D.density b x) ∧
--         (∀ p∈Y,∀ z y,y∈(extChartAt 𝓘(ℝ,Plane) z).target→
--           (extChartAt 𝓘(ℝ,Plane) z).symm y∈K→
--           0 < chartTwoForm (manifoldExteriorOneForm (Γ₁ p)) z y (1,0) (0,1)) ∧
--         (∀ p x,x∈D.chart.target→s (p,x)=q) ∧
--         (∀ x∈D.chart.target,ContDiffAt ℝ ∞
--           (chartOneForm γ x) (extChartAt 𝓘(ℝ,Plane) x x)) ∧
--         (∀ x∈D.chart.target,manifoldExteriorOneForm γ x=q • Λ x) ∧
--         (∀ p,∀ x∈W,Γ₁ p x=γ x+
--           (intervalClock (-b) b (D.chart.symm x).1*H p) • D.dual x) ∧
--         (∀ p∈Y,∀ x∈K,0 < s (p,x)) ∧
--         (∀ p∈Y,restrictedPartitionFormMass B ρ K (fun x => s (p,x) • Λ x)<ε) ∧
--         (∃ U : Set M,IsOpen U ∧ frontier K⊆U ∧ ∀ p x,x∈U→s (p,x)=c (p,x))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.Hamiltonian.CircleModel`, `OAI.PackingSufficiencySupport.Hamiltonian.CylinderModel`, `OAI.PackingSufficiencySupport.Hamiltonian.HandleCylinder`, `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldTwoForm`, `OAI.PackingSufficiencySupport.Hamiltonian.Plane`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothOneFormFamily`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothTwoForm`, `OAI.PackingSufficiencySupport.Hamiltonian.SurfaceCoordinateBox`, `OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.chartTwoForm`, `OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace`, `OAI.PackingSufficiencySupport.Hamiltonian.intervalClock`, `OAI.PackingSufficiencySupport.Hamiltonian.manifoldExteriorOneForm` and `OAI.PackingSufficiencySupport.Hamiltonian.SurfaceCoordinateBox.carrier` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.PositivePartialChart` and `OAI.PackingSufficiencySupport.Hamiltonian.PositivePlaneTransitions` (definitions bundle `OAIQ240Bp007` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.restrictedPartitionFormMass` (definitions bundle `OAIQ240Bp010` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData` and `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart` (definitions bundle `OAIQ240Bp015` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.band` and `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.density` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proof of `OAI.PackingSufficiencySupport.MomentPolytope.Annular.exhausted_surface_packing_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Hamiltonian/AnnularDensityMass.lean (declaration OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.exists_surface_step_two)

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
section

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {M : Type} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [TopologicalSpace.PseudoMetrizableSpace M] [MeasurableSpace M] [BorelSpace M]
  {I : Type*} [Fintype I] {K : Set M}

theorem exists_surface_step_two_bp240
    (hK : IsCompact K) (hc : IsPreconnected (interior K)) (hne : (interior K).Nonempty)
    (hor : PositivePlaneTransitions M)
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    (hnull : ∀ i,volume ((extChartAt 𝓘(ℝ,Plane) (B i).center).target ∩
      (extChartAt 𝓘(ℝ,Plane) (B i).center).symm ⁻¹' frontier K)=0)
    (D : AnnularHandleData Plane M) {b : ℝ} (hb : 0<b) (hbw : b<D.width)
    (heK : closure D.chart.target⊆interior K) (hβK : tsupport D.dual⊆interior K)
    (heor : PositivePartialChart D.densityChart)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hsΛ : ∀ x u v,Λ x u v= -Λ x v u)
    (hpΛ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0 < chartTwoForm Λ c y (1,0) (0,1))
    {c : P × M → ℝ} (hs : ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ c)
    {Y : Set P} (hY : IsCompact Y) (hcp : ∀ p∈Y,∀ x∈K,0 < c (p,x))
    {Γ₀ : P → ManifoldOneForm Plane M} (hΓ₀ : SmoothOneFormFamily Γ₀)
    (hdΓ₀ : ∀ p x,manifoldExteriorOneForm (Γ₀ p) x=c (p,x) • Λ x)
    {A : P → ℝ} {ε : ℝ} (hε : 0<ε) (hA : ∀ p∈Y,2*ε<A p)
    (herr : ∀ p∈Y,|restrictedPartitionFormMass B ρ K (fun x => c (p,x) • Λ x)-A p|<ε) :
    ∃ (q : ℝ) (s : P × M → ℝ) (H : P → ℝ)
      (Γ₁ : P → ManifoldOneForm Plane M) (γ : ManifoldOneForm Plane M) (L W : Set M),
      0<q ∧ ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ s ∧ ContDiff ℝ ∞ H ∧
      (∀ p,H p=restrictedPartitionFormMass B ρ K (fun x => c (p,x) • Λ x)-
        restrictedPartitionFormMass B ρ K (fun x => s (p,x) • Λ x)) ∧
      (∀ p∈Y,0<H p ∧ |H p-A p|<2*ε) ∧
      SmoothOneFormFamily Γ₁ ∧ IsCompact L ∧ L⊆interior K ∧ IsOpen W ∧
      D.chart '' band b⊆W ∧ W⊆D.chart.target ∧
      (∀ p x,x∉L→Γ₁ p x=Γ₀ p x) ∧
      (∀ p x,x∈K→manifoldExteriorOneForm (Γ₁ p) x=
        s (p,x) • Λ x+H p • D.density b x) ∧
      (∀ p∈Y,∀ z y,y∈(extChartAt 𝓘(ℝ,Plane) z).target→
        (extChartAt 𝓘(ℝ,Plane) z).symm y∈K→
        0 < chartTwoForm (manifoldExteriorOneForm (Γ₁ p)) z y (1,0) (0,1)) ∧
      (∀ p x,x∈D.chart.target→s (p,x)=q) ∧
      (∀ x∈D.chart.target,ContDiffAt ℝ ∞
        (chartOneForm γ x) (extChartAt 𝓘(ℝ,Plane) x x)) ∧
      (∀ x∈D.chart.target,manifoldExteriorOneForm γ x=q • Λ x) ∧
      (∀ p,∀ x∈W,Γ₁ p x=γ x+
        (intervalClock (-b) b (D.chart.symm x).1*H p) • D.dual x) ∧
      (∀ p∈Y,∀ x∈K,0 < s (p,x)) ∧
      (∀ p∈Y,restrictedPartitionFormMass B ρ K (fun x => s (p,x) • Λ x)<ε) ∧
      (∃ U : Set M,IsOpen U ∧ frontier K⊆U ∧ ∀ p x,x∈U→s (p,x)=c (p,x)) := by
  sorry

end

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

end

end OAI
end
