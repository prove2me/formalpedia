-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_MomentPolytope_finite_surface_comparison_bp240
-- name    : OAI.PackingSufficiencySupport.MomentPolytope.finite_surface_comparison_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:56:03.65721+00:00
-- url     : https://prove2.me/theorems/0c585db7-bb4f-4a1c-b887-fae458186d1b
-- title:
--   OAI.PackingSufficiencySupport.MomentPolytope.finite_surface_comparison_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.MomentPolytope.finite_surface_comparison` of [lean/OAI/Geometry/BallPacking/Models/SurfaceComparison.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Models/SurfaceComparison.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.MomentPolytope`, with `open scoped ContDiff Topology BigOperators Pointwise`, `open Set Function MeasureTheory`, `open Hamiltonian Comparison`):
--
--   ```lean
--   theorem finite_surface_comparison_bp240 {m N : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
--       (b : Fin N → Moments m) (c : Fin N → ℝ)
--       (hb : ∀ ν j,0 ≤ b ν j) (hc : ∀ ν,0 < c ν) (hcomp : IsCompact (region b c))
--       (H : Moments m → ℝ) (hH : ContinuousOn H (region b c))
--       (hHpos : ∀ p ∈ region b c,0<H p) (r : ι → ℝ)
--       (hconc : ConcaveOn ℝ (region b c) (fun p => H p-∑ i,max (r i-∑ j,p j) 0))
--       (hmean : 0 < ∫ p in region b c,H p-∑ i,max (r i-∑ j,p j) 0)
--       {τ a : ℝ} (hτ : 0<τ) (hτ1 : τ<1) (ha : 0<a)
--       (houter : ∀ p ∈ region b c,p ∉ τ • region b c → a ≤ H p-∑ i,max (r i-∑ j,p j) 0) :
--       ∃ (K : Moments m → ℝ) (Φ : CompactHamiltonianIsotopy (@phaseArea (Fin m) _))
--         (g ε : ℝ) (h : ι → Moments m → ℝ),
--         ContDiff ℝ ∞ K ∧ 0<g ∧ 0<ε ∧ 8*ε<g ∧
--         (∀ p ∈ region b c,8*ε<H p) ∧
--         (∀ i,ContDiff ℝ ∞ (h i)) ∧
--         (∀ i p,max (r i-∑ j,p j) 0<h i p) ∧
--         (∀ p,0<(∑ i,h i p)-(∑ i,max (r i-∑ j,p j) 0) ∧
--           (∑ i,h i p)-(∑ i,max (r i-∑ j,p j) 0)<ε) ∧
--         (∀ t z,Φ.map t z ∈ planeRegion b c ↔ z ∈ planeRegion b c) ∧
--         (∀ ν,∃ ρ>0,∀ t z,c ν-weightedMoment (b ν) z<ρ →
--           fderiv ℝ (weightedMoment (b ν)) z (hamiltonianField phaseArea Φ.hamiltonian (t,z))=0) ∧
--         (∀ Hstar : Moments m → ℝ,(∀ p ∈ region b c,|Hstar p-H p|<2*ε) →
--           (∀ p ∈ region b c,0<Hstar p) ∧
--           ∀ v ∈ planeRegion b c,g/2 < surfaceRemainder (K ∘ planeMoments)
--             (Hstar ∘ planeMoments) (fun i => h i ∘ planeMoments) (Φ.map 1).symm v)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.Hamiltonian.CompactHamiltonianIsotopy`, `OAI.PackingSufficiencySupport.Hamiltonian.Plane`, `OAI.PackingSufficiencySupport.Hamiltonian.PlanePhase`, `OAI.PackingSufficiencySupport.Hamiltonian.hamiltonianField`, `OAI.PackingSufficiencySupport.Hamiltonian.phaseArea`, `OAI.PackingSufficiencySupport.Hamiltonian.surfaceRemainder` and `OAI.PackingSufficiencySupport.MomentPolytope.Moments` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.MomentPolytope.region` (definitions bundle `OAIQ240Bp007` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.planeMoments` (definitions bundle `OAIQ240Bp010` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.weightedMoment` (definitions bundle `OAIQ240Bp015` of this split); `OAI.PackingSufficiencySupport.MomentPolytope.planeRegion` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proof of `OAI.PackingSufficiencySupport.MomentPolytope.Annular.exhausted_surface_packing_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Models/SurfaceComparison.lean (declaration OAI.PackingSufficiencySupport.MomentPolytope.finite_surface_comparison)

import Mathlib
import Definitions.Def_OAIQ240Bp019

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.MomentPolytope
open scoped ContDiff Topology BigOperators Pointwise
open Set Function MeasureTheory
open Hamiltonian Comparison

theorem finite_surface_comparison_bp240 {m N : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (b : Fin N → Moments m) (c : Fin N → ℝ)
    (hb : ∀ ν j,0 ≤ b ν j) (hc : ∀ ν,0 < c ν) (hcomp : IsCompact (region b c))
    (H : Moments m → ℝ) (hH : ContinuousOn H (region b c))
    (hHpos : ∀ p ∈ region b c,0<H p) (r : ι → ℝ)
    (hconc : ConcaveOn ℝ (region b c) (fun p => H p-∑ i,max (r i-∑ j,p j) 0))
    (hmean : 0 < ∫ p in region b c,H p-∑ i,max (r i-∑ j,p j) 0)
    {τ a : ℝ} (hτ : 0<τ) (hτ1 : τ<1) (ha : 0<a)
    (houter : ∀ p ∈ region b c,p ∉ τ • region b c → a ≤ H p-∑ i,max (r i-∑ j,p j) 0) :
    ∃ (K : Moments m → ℝ) (Φ : CompactHamiltonianIsotopy (@phaseArea (Fin m) _))
      (g ε : ℝ) (h : ι → Moments m → ℝ),
      ContDiff ℝ ∞ K ∧ 0<g ∧ 0<ε ∧ 8*ε<g ∧
      (∀ p ∈ region b c,8*ε<H p) ∧
      (∀ i,ContDiff ℝ ∞ (h i)) ∧
      (∀ i p,max (r i-∑ j,p j) 0<h i p) ∧
      (∀ p,0<(∑ i,h i p)-(∑ i,max (r i-∑ j,p j) 0) ∧
        (∑ i,h i p)-(∑ i,max (r i-∑ j,p j) 0)<ε) ∧
      (∀ t z,Φ.map t z ∈ planeRegion b c ↔ z ∈ planeRegion b c) ∧
      (∀ ν,∃ ρ>0,∀ t z,c ν-weightedMoment (b ν) z<ρ →
        fderiv ℝ (weightedMoment (b ν)) z (hamiltonianField phaseArea Φ.hamiltonian (t,z))=0) ∧
      (∀ Hstar : Moments m → ℝ,(∀ p ∈ region b c,|Hstar p-H p|<2*ε) →
        (∀ p ∈ region b c,0<Hstar p) ∧
        ∀ v ∈ planeRegion b c,g/2 < surfaceRemainder (K ∘ planeMoments)
          (Hstar ∘ planeMoments) (fun i => h i ∘ planeMoments) (Φ.map 1).symm v) := by
  sorry

end PackingSufficiencySupport.MomentPolytope

end

end OAI
end
