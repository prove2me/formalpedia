-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_AnnularHandleData_globalSurfaceSecondPath_isInvertible_annular_bp240
-- name    : OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPath_isInvertible_annular_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:55:11.748549+00:00
-- url     : https://prove2.me/theorems/3b12cca4-de8e-443c-a667-e4b76335c21c
-- title:
--   OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPath_isInvertible_annular_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPath_isInvertible_annular` of [lean/OAI/Geometry/BallPacking/SurfaceArea/AnnularSecondPositivity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/SurfaceArea/AnnularSecondPositivity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData`, with `open scoped ContDiff Manifold Topology`, `open Set Function Manifold`):
--
--   ```lean
--   theorem globalSurfaceSecondPath_isInvertible_annular_bp240 {ι : Type*} [Fintype ι]
--       (hΩ : Ω.IsInvertible) (hskew : ∀ v w,Ω v w= -Ω w v)
--       (D : AnnularHandleData E M)
--       {b : ℝ} (hb : 0<b) (hbw : b<D.width)
--       (Φ : CompactHamiltonianIsotopy Ω) {K H : V → ℝ}
--       (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H)
--       {h : ι → V → ℝ} (hh : ∀ i,ContDiff ℝ ∞ (h i))
--       {ρ : ι → ℝ → ℝ} (hρ : ∀ i,ContDiff ℝ ∞ (ρ i))
--       {ρ₀ : ℝ → ℝ} (hρ₀ : ContDiff ℝ ∞ ρ₀)
--       (hlo : ∀ s,s ≤ -b →(∀ i,ρ i s=0) ∧ ρ₀ s=0)
--       (hhi : ∀ s,b ≤ s →(∀ i,ρ i s=1) ∧ ρ₀ s=1)
--       {Γ : V → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
--       {γ : ManifoldOneForm E M}
--       (hγ : ∀ x∈D.chart.target,ContDiffAt ℝ ∞
--         (chartOneForm γ x) (extChartAt 𝓘(ℝ,E) x x))
--       {W : Set M} (hW : IsOpen W)
--       (hN : ∀ v x,x∈W→Γ v x=γ x+
--         (intervalClock (-b) b (D.chart.symm x).1*H v) • D.dual x)
--       (τ : ℝ) (hτ : τ∈Icc (0:ℝ) 1) (p : Plane × V) (hp : p.1∈D.annularCoverDomain)
--       (hx : D.handleAnnularCover p.1∈W)
--       (hbase : 0 < manifoldExteriorOneForm γ (D.handleAnnularCover p.1)
--         (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (D.handleAnnularCover) p.1 (1,0))
--         (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (D.handleAnnularCover) p.1 (0,1)))
--       (hfp : 0≤D.clock (circleTurn p.1.2))
--       (hHp : 0≤H ((Φ.map 1).symm (Φ.map (intervalClock (-b) b p.1.1) p.2)))
--       (hclock : ∀ i,0≤deriv (ρ i) p.1.1) (hclock₀ : 0≤deriv ρ₀ p.1.1)
--       (hcap : ∀ i,0≤h i (Φ.map (intervalClock (-b) b p.1.1) p.2))
--       (hres : 0 ≤ surfaceRemainder K H h (Φ.map 1).symm
--         (Φ.map (intervalClock (-b) b p.1.1) p.2)) :
--       (globalHorizontalCoupling Ω
--         (fun v => globalSurfaceSecondPrimitive D b Φ K H h ρ ρ₀ Γ (τ,v))
--         (D.handleAnnularCover p.1,p.2)).IsInvertible
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.Hamiltonian.CircleModel`, `OAI.PackingSufficiencySupport.Hamiltonian.CompactHamiltonianIsotopy`, `OAI.PackingSufficiencySupport.Hamiltonian.CylinderModel`, `OAI.PackingSufficiencySupport.Hamiltonian.HandleCylinder`, `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.Plane`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothOneFormFamily`, `OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.circleTurn`, `OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace`, `OAI.PackingSufficiencySupport.Hamiltonian.intervalClock`, `OAI.PackingSufficiencySupport.Hamiltonian.manifoldExteriorOneForm` and `OAI.PackingSufficiencySupport.Hamiltonian.surfaceRemainder` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.globalHorizontalCoupling` (definitions bundle `OAIQ240Bp010` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData`, `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive` and `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover` (definitions bundle `OAIQ240Bp015` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularCoverDomain` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proof of `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPath_isInvertible_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/SurfaceArea/AnnularSecondPositivity.lean (declaration OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPath_isInvertible_annular)

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

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ}

theorem globalSurfaceSecondPath_isInvertible_annular_bp240 {ι : Type*} [Fintype ι]
    (hΩ : Ω.IsInvertible) (hskew : ∀ v w,Ω v w= -Ω w v)
    (D : AnnularHandleData E M)
    {b : ℝ} (hb : 0<b) (hbw : b<D.width)
    (Φ : CompactHamiltonianIsotopy Ω) {K H : V → ℝ}
    (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H)
    {h : ι → V → ℝ} (hh : ∀ i,ContDiff ℝ ∞ (h i))
    {ρ : ι → ℝ → ℝ} (hρ : ∀ i,ContDiff ℝ ∞ (ρ i))
    {ρ₀ : ℝ → ℝ} (hρ₀ : ContDiff ℝ ∞ ρ₀)
    (hlo : ∀ s,s ≤ -b →(∀ i,ρ i s=0) ∧ ρ₀ s=0)
    (hhi : ∀ s,b ≤ s →(∀ i,ρ i s=1) ∧ ρ₀ s=1)
    {Γ : V → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    {γ : ManifoldOneForm E M}
    (hγ : ∀ x∈D.chart.target,ContDiffAt ℝ ∞
      (chartOneForm γ x) (extChartAt 𝓘(ℝ,E) x x))
    {W : Set M} (hW : IsOpen W)
    (hN : ∀ v x,x∈W→Γ v x=γ x+
      (intervalClock (-b) b (D.chart.symm x).1*H v) • D.dual x)
    (τ : ℝ) (hτ : τ∈Icc (0:ℝ) 1) (p : Plane × V) (hp : p.1∈D.annularCoverDomain)
    (hx : D.handleAnnularCover p.1∈W)
    (hbase : 0 < manifoldExteriorOneForm γ (D.handleAnnularCover p.1)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (D.handleAnnularCover) p.1 (1,0))
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (D.handleAnnularCover) p.1 (0,1)))
    (hfp : 0≤D.clock (circleTurn p.1.2))
    (hHp : 0≤H ((Φ.map 1).symm (Φ.map (intervalClock (-b) b p.1.1) p.2)))
    (hclock : ∀ i,0≤deriv (ρ i) p.1.1) (hclock₀ : 0≤deriv ρ₀ p.1.1)
    (hcap : ∀ i,0≤h i (Φ.map (intervalClock (-b) b p.1.1) p.2))
    (hres : 0 ≤ surfaceRemainder K H h (Φ.map 1).symm
      (Φ.map (intervalClock (-b) b p.1.1) p.2)) :
    (globalHorizontalCoupling Ω
      (fun v => globalSurfaceSecondPrimitive D b Φ K H h ρ ρ₀ Γ (τ,v))
      (D.handleAnnularCover p.1,p.2)).IsInvertible := by
  sorry

end

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

end

end OAI
end
