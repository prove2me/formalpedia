-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_AnnularHandleData_globalSurfaceSecondPath_isInvertible_bp240
-- name    : OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPath_isInvertible_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:55:22.778929+00:00
-- url     : https://prove2.me/theorems/13fcb3f3-871e-400e-b2c6-d1d82456ace4
-- title:
--   OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPath_isInvertible_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPath_isInvertible` of [lean/OAI/Geometry/BallPacking/SurfaceArea/AnnularSecondPositivity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/SurfaceArea/AnnularSecondPositivity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData`, with `open scoped ContDiff Manifold Topology`, `open Set Function Manifold`):
--
--   ```lean
--    theorem globalSurfaceSecondPath_isInvertible_bp240 {κ : Type*} [Fintype κ]
--       (D : AnnularHandleData Plane M)
--       {b : ℝ} (hb : 0<b) (hbw : b<D.width)
--       (hor : PositivePartialChart D.densityChart)
--       {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
--       (hsΛ : ∀ x u v,Λ x u v= -Λ x v u)
--       (hpΛ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→0 < chartTwoForm Λ c y (1,0) (0,1))
--       {r : ℝ} (hr : 0 < r) {γ : ManifoldOneForm Plane M}
--       (hγ : ∀ x∈D.chart.target,ContDiffAt ℝ ∞
--         (chartOneForm γ x) (extChartAt 𝓘(ℝ,Plane) x x))
--       (hdγ : ∀ x∈D.chart.target,manifoldExteriorOneForm γ x=r • Λ x)
--       {Γ : (ι → ℝ) → ManifoldOneForm Plane M} (hΓ : SmoothOneFormFamily Γ)
--       {K H : (ι → ℝ) → ℝ} (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H) {Y : Set (ι → ℝ)} (hHp : ∀ p∈Y,0≤H p)
--       {Kbase : Set M}
--       (hbase : ∀ p∈Y,∀ x∈Kbase,0 < chartTwoForm (manifoldExteriorOneForm (Γ p)) x
--         (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1))
--       {W : Set M} (hW : IsOpen W) (hBW : D.chart '' band b⊆W)
--       (hWA : W⊆D.chart.target)
--       (hN : ∀ p x,x∈W→Γ p x=γ x+
--         (intervalClock (-b) b (D.chart.symm x).1*H p) • D.dual x)
--       (Φ : CompactHamiltonianIsotopy (phaseArea (ι := ι)))
--       (hΦ : ∀ t∈Icc (0:ℝ) 1,MapsTo (Φ.map t) (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y) ∧
--         MapsTo (Φ.map t).symm (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y))
--       {h : κ → PlanePhase ι → ℝ} (hh : ∀ i,ContDiff ℝ ∞ (h i))
--       {ρ : κ → ℝ → ℝ} (hρ : ∀ i,ContDiff ℝ ∞ (ρ i))
--       {ρ₀ : ℝ → ℝ} (hρ₀ : ContDiff ℝ ∞ ρ₀)
--       (hlo : ∀ s,s ≤ -b →(∀ i,ρ i s=0) ∧ ρ₀ s=0)
--       (hhi : ∀ s,b ≤ s →(∀ i,ρ i s=1) ∧ ρ₀ s=1)
--       (hclock : ∀ i s,0≤deriv (ρ i) s) (hclock₀ : ∀ s,0≤deriv ρ₀ s)
--       (hcap : ∀ v,planeMoments v∈Y→∀ i,0≤h i v)
--       (hres : ∀ v,planeMoments v∈Y→0 ≤ surfaceRemainder (K ∘ planeMoments) (H ∘ planeMoments) h (Φ.map 1).symm v)
--       {τ : ℝ} (hτ : τ∈Icc (0:ℝ) 1) {z : M × PlanePhase ι} (hz : z∈Kbase ×ˢ (planeMoments ⁻¹' Y)) :
--       (globalHorizontalCoupling phaseArea (fun v =>
--         globalSurfaceSecondPrimitive D b Φ (K ∘ planeMoments) (H ∘ planeMoments) h ρ ρ₀
--           (Γ ∘ planeMoments) (τ,v)) z).IsInvertible
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.Hamiltonian.CircleModel`, `OAI.PackingSufficiencySupport.Hamiltonian.CompactHamiltonianIsotopy`, `OAI.PackingSufficiencySupport.Hamiltonian.CylinderModel`, `OAI.PackingSufficiencySupport.Hamiltonian.HandleCylinder`, `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldTwoForm`, `OAI.PackingSufficiencySupport.Hamiltonian.Plane`, `OAI.PackingSufficiencySupport.Hamiltonian.PlanePhase`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothOneFormFamily`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothTwoForm`, `OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.chartTwoForm`, `OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace`, `OAI.PackingSufficiencySupport.Hamiltonian.intervalClock`, `OAI.PackingSufficiencySupport.Hamiltonian.manifoldExteriorOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.phaseArea` and `OAI.PackingSufficiencySupport.Hamiltonian.surfaceRemainder` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.PositivePartialChart` (definitions bundle `OAIQ240Bp007` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.globalHorizontalCoupling` and `OAI.PackingSufficiencySupport.Hamiltonian.planeMoments` (definitions bundle `OAIQ240Bp010` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData`, `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart` and `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive` (definitions bundle `OAIQ240Bp015` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.band` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proof of `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.exists_surface_normal_form_packing_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/SurfaceArea/AnnularSecondPositivity.lean (declaration OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPath_isInvertible)

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
open Set Function Manifold
section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]

 theorem globalSurfaceSecondPath_isInvertible_bp240 {κ : Type*} [Fintype κ]
    (D : AnnularHandleData Plane M)
    {b : ℝ} (hb : 0<b) (hbw : b<D.width)
    (hor : PositivePartialChart D.densityChart)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hsΛ : ∀ x u v,Λ x u v= -Λ x v u)
    (hpΛ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→0 < chartTwoForm Λ c y (1,0) (0,1))
    {r : ℝ} (hr : 0 < r) {γ : ManifoldOneForm Plane M}
    (hγ : ∀ x∈D.chart.target,ContDiffAt ℝ ∞
      (chartOneForm γ x) (extChartAt 𝓘(ℝ,Plane) x x))
    (hdγ : ∀ x∈D.chart.target,manifoldExteriorOneForm γ x=r • Λ x)
    {Γ : (ι → ℝ) → ManifoldOneForm Plane M} (hΓ : SmoothOneFormFamily Γ)
    {K H : (ι → ℝ) → ℝ} (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H) {Y : Set (ι → ℝ)} (hHp : ∀ p∈Y,0≤H p)
    {Kbase : Set M}
    (hbase : ∀ p∈Y,∀ x∈Kbase,0 < chartTwoForm (manifoldExteriorOneForm (Γ p)) x
      (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1))
    {W : Set M} (hW : IsOpen W) (hBW : D.chart '' band b⊆W)
    (hWA : W⊆D.chart.target)
    (hN : ∀ p x,x∈W→Γ p x=γ x+
      (intervalClock (-b) b (D.chart.symm x).1*H p) • D.dual x)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := ι)))
    (hΦ : ∀ t∈Icc (0:ℝ) 1,MapsTo (Φ.map t) (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y) ∧
      MapsTo (Φ.map t).symm (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y))
    {h : κ → PlanePhase ι → ℝ} (hh : ∀ i,ContDiff ℝ ∞ (h i))
    {ρ : κ → ℝ → ℝ} (hρ : ∀ i,ContDiff ℝ ∞ (ρ i))
    {ρ₀ : ℝ → ℝ} (hρ₀ : ContDiff ℝ ∞ ρ₀)
    (hlo : ∀ s,s ≤ -b →(∀ i,ρ i s=0) ∧ ρ₀ s=0)
    (hhi : ∀ s,b ≤ s →(∀ i,ρ i s=1) ∧ ρ₀ s=1)
    (hclock : ∀ i s,0≤deriv (ρ i) s) (hclock₀ : ∀ s,0≤deriv ρ₀ s)
    (hcap : ∀ v,planeMoments v∈Y→∀ i,0≤h i v)
    (hres : ∀ v,planeMoments v∈Y→0 ≤ surfaceRemainder (K ∘ planeMoments) (H ∘ planeMoments) h (Φ.map 1).symm v)
    {τ : ℝ} (hτ : τ∈Icc (0:ℝ) 1) {z : M × PlanePhase ι} (hz : z∈Kbase ×ˢ (planeMoments ⁻¹' Y)) :
    (globalHorizontalCoupling phaseArea (fun v =>
      globalSurfaceSecondPrimitive D b Φ (K ∘ planeMoments) (H ∘ planeMoments) h ρ ρ₀
        (Γ ∘ planeMoments) (τ,v)) z).IsInvertible := by
  sorry

end

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

end

end OAI
end
