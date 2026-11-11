-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_AnnularHandleData_globalSurfaceFirstPath_moser_endpoint_bp240
-- name    : OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPath_moser_endpoint_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:54:44.536685+00:00
-- url     : https://prove2.me/theorems/89e5a080-2dfb-4e8a-9269-a63b587280b4
-- title:
--   OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPath_moser_endpoint_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPath_moser_endpoint` of [lean/OAI/Geometry/BallPacking/Toric/ToricClosedShift.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Toric/ToricClosedShift.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData`, with `open scoped ContDiff Manifold Topology BigOperators`, `open Set Function Manifold`):
--
--   ```lean
--    theorem globalSurfaceFirstPath_moser_endpoint_bp240
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
--       {H : (ι → ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) {Y : Set (ι → ℝ)} (hHp : ∀ p∈Y,0≤H p)
--       {Kbase : Set M} (heD : D.chart.target⊆interior Kbase)
--       (hbase : ∀ p∈Y,∀ x∈Kbase,0 < chartTwoForm (manifoldExteriorOneForm (Γ p)) x
--         (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1))
--       {W : Set M} (hW : IsOpen W) (hBW : D.chart '' band b⊆W)
--       (hWA : W⊆D.chart.target)
--       (hN : ∀ p x,x∈W→Γ p x=γ x+
--         (intervalClock (-b) b (D.chart.symm x).1*H p) • D.dual x)
--       (Φ : CompactHamiltonianIsotopy (phaseArea (ι := ι)))
--       (hΦ : ∀ t∈Icc (0:ℝ) 1,MapsTo (Φ.map t) (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y) ∧
--         MapsTo (Φ.map t).symm (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y))
--       {J : Type*} (F : J → (ι → ℝ) → ℝ) (hF : ∀ j,ContDiff ℝ ∞ (F j))
--       (α c : J → ℝ) (hαc : ∀ j,α j < c j)
--       (hYeq : planeMoments ⁻¹' Y={v | ∀ j,(F j ∘ planeMoments) v ≤ c j})
--       (hYC : IsCompact (planeMoments ⁻¹' Y))
--       (hzero : ∀ j t v,α j<(F j ∘ planeMoments) v→
--         fderiv ℝ (F j ∘ planeMoments) v (hamiltonianField phaseArea Φ.hamiltonian (t,v))=0) :
--       ∃ ψ : (M × PlanePhase ι) ≃ₘ⟮𝓘(ℝ,Plane × PlanePhase ι),𝓘(ℝ,Plane × PlanePhase ι)⟯ (M × PlanePhase ι),
--         ψ '' (Kbase ×ˢ (planeMoments ⁻¹' Y))=Kbase ×ˢ (planeMoments ⁻¹' Y) ∧
--         ψ '' interior (Kbase ×ˢ (planeMoments ⁻¹' Y))=interior (Kbase ×ˢ (planeMoments ⁻¹' Y)) ∧
--         PreservesTwoFormOn ψ (globalHorizontalCoupling phaseArea (Γ ∘ planeMoments))
--           (globalHorizontalCoupling phaseArea (fun v =>
--             globalSurfaceFirstPrimitive D b Φ (H ∘ planeMoments) (Γ ∘ planeMoments) (1,v)))
--           (Kbase ×ˢ (planeMoments ⁻¹' Y)) ∧
--         (∃ C : Set (M × PlanePhase ι),IsCompact C ∧ ∀ z,z∉C→ψ z=z) ∧
--         (∀ z,z.1∉D.chart '' band b→ψ z=z)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.Hamiltonian.CircleModel`, `OAI.PackingSufficiencySupport.Hamiltonian.CompactHamiltonianIsotopy`, `OAI.PackingSufficiencySupport.Hamiltonian.CylinderModel`, `OAI.PackingSufficiencySupport.Hamiltonian.HandleCylinder`, `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldTwoForm`, `OAI.PackingSufficiencySupport.Hamiltonian.Plane`, `OAI.PackingSufficiencySupport.Hamiltonian.PlanePhase`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothOneFormFamily`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothTwoForm`, `OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.chartTwoForm`, `OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace`, `OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace`, `OAI.PackingSufficiencySupport.Hamiltonian.hamiltonianField`, `OAI.PackingSufficiencySupport.Hamiltonian.intervalClock`, `OAI.PackingSufficiencySupport.Hamiltonian.manifoldExteriorOneForm` and `OAI.PackingSufficiencySupport.Hamiltonian.phaseArea` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.PositivePartialChart` and `OAI.PackingSufficiencySupport.Hamiltonian.PreservesTwoFormOn` (definitions bundle `OAIQ240Bp007` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.globalHorizontalCoupling` and `OAI.PackingSufficiencySupport.Hamiltonian.planeMoments` (definitions bundle `OAIQ240Bp010` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData`, `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart` and `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive` (definitions bundle `OAIQ240Bp015` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.band` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proof of `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.exists_surface_normal_form_packing_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Toric/ToricClosedShift.lean (declaration OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPath_moser_endpoint)

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
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [T2Space M] [NormalSpace M] [SigmaCompactSpace M]

 theorem globalSurfaceFirstPath_moser_endpoint_bp240
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
    {H : (ι → ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) {Y : Set (ι → ℝ)} (hHp : ∀ p∈Y,0≤H p)
    {Kbase : Set M} (heD : D.chart.target⊆interior Kbase)
    (hbase : ∀ p∈Y,∀ x∈Kbase,0 < chartTwoForm (manifoldExteriorOneForm (Γ p)) x
      (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1))
    {W : Set M} (hW : IsOpen W) (hBW : D.chart '' band b⊆W)
    (hWA : W⊆D.chart.target)
    (hN : ∀ p x,x∈W→Γ p x=γ x+
      (intervalClock (-b) b (D.chart.symm x).1*H p) • D.dual x)
    (Φ : CompactHamiltonianIsotopy (phaseArea (ι := ι)))
    (hΦ : ∀ t∈Icc (0:ℝ) 1,MapsTo (Φ.map t) (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y) ∧
      MapsTo (Φ.map t).symm (planeMoments ⁻¹' Y) (planeMoments ⁻¹' Y))
    {J : Type*} (F : J → (ι → ℝ) → ℝ) (hF : ∀ j,ContDiff ℝ ∞ (F j))
    (α c : J → ℝ) (hαc : ∀ j,α j < c j)
    (hYeq : planeMoments ⁻¹' Y={v | ∀ j,(F j ∘ planeMoments) v ≤ c j})
    (hYC : IsCompact (planeMoments ⁻¹' Y))
    (hzero : ∀ j t v,α j<(F j ∘ planeMoments) v→
      fderiv ℝ (F j ∘ planeMoments) v (hamiltonianField phaseArea Φ.hamiltonian (t,v))=0) :
    ∃ ψ : (M × PlanePhase ι) ≃ₘ⟮𝓘(ℝ,Plane × PlanePhase ι),𝓘(ℝ,Plane × PlanePhase ι)⟯ (M × PlanePhase ι),
      ψ '' (Kbase ×ˢ (planeMoments ⁻¹' Y))=Kbase ×ˢ (planeMoments ⁻¹' Y) ∧
      ψ '' interior (Kbase ×ˢ (planeMoments ⁻¹' Y))=interior (Kbase ×ˢ (planeMoments ⁻¹' Y)) ∧
      PreservesTwoFormOn ψ (globalHorizontalCoupling phaseArea (Γ ∘ planeMoments))
        (globalHorizontalCoupling phaseArea (fun v =>
          globalSurfaceFirstPrimitive D b Φ (H ∘ planeMoments) (Γ ∘ planeMoments) (1,v)))
        (Kbase ×ˢ (planeMoments ⁻¹' Y)) ∧
      (∃ C : Set (M × PlanePhase ι),IsCompact C ∧ ∀ z,z∉C→ψ z=z) ∧
      (∀ z,z.1∉D.chart '' band b→ψ z=z) := by
  sorry

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData
end

end OAI
end
