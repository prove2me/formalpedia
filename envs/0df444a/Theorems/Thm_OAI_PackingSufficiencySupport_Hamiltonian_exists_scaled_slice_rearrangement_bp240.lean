-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_exists_scaled_slice_rearrangement_bp240
-- name    : OAI.PackingSufficiencySupport.Hamiltonian.exists_scaled_slice_rearrangement_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:56:39.774486+00:00
-- url     : https://prove2.me/theorems/86c10766-b5f0-4789-94dd-b694041256f1
-- title:
--   OAI.PackingSufficiencySupport.Hamiltonian.exists_scaled_slice_rearrangement_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.Hamiltonian.exists_scaled_slice_rearrangement` of [lean/OAI/Geometry/BallPacking/Hamiltonian/LiftedCompact.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Hamiltonian/LiftedCompact.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.Hamiltonian`, with `open scoped ContDiff Topology`, `open Set Function`, `open Comparison`, `open scoped BigOperators`, `open MeasureTheory`):
--
--   ```lean
--   theorem exists_scaled_slice_rearrangement_bp240 {Y : Set P} (hY : IsCompact Y)
--       {L : P → ℝ} (hL : Continuous L) (hcL : ConcaveOn ℝ Y L)
--       (F : C(P × ℝ,ℝ))
--       (hconv : ∀ y ∈ Y, ConvexOn ℝ (Icc 0 (L y)) (fun v => F (y,v)))
--       {ε : ℝ} (he : 0 < ε) :
--       ∃ (a χ : P → ℝ) (Ψ : HamiltonianDiskIsotopyFamily P (areaRadius 1)),
--         ContDiff ℝ ∞ a ∧ (∀ y, 0 < a y) ∧ ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
--         (∀ y, χ y ∈ Icc 0 1) ∧
--         (∀ y ∈ tsupport χ, (a y)^2 < L y) ∧
--         (∀ y ∈ Y, ∀ t x, radialArea x ≤ L y →
--           radialArea (scaledPlanarTrace Ψ.motion a χ y t x) ≤ L y) ∧
--         (∀ y ∈ Y, ∀ x, radialArea x ≤ L y →
--           F (y,radialArea (scaledPlanarTrace Ψ.motion a χ y 1 x)) ≤
--             intervalMinimum (fiberFunction F y) (L y) (radialArea x)+ε)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.Comparison.fiberFunction` and `OAI.PackingSufficiencySupport.Hamiltonian.Plane` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.areaRadius` (definitions bundle `OAIQ240Bp004` of this split); `OAI.PackingSufficiencySupport.Comparison.intervalMinimum` (definitions bundle `OAIQ240Bp006` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.HamiltonianDiskIsotopyFamily` and `OAI.PackingSufficiencySupport.Hamiltonian.radialArea` (definitions bundle `OAIQ240Bp010` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.scaledPlanarTrace` and `OAI.PackingSufficiencySupport.Hamiltonian.HamiltonianDiskIsotopyFamily.motion` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proof of `OAI.PackingSufficiencySupport.MomentPolytope.finite_surface_comparison_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Hamiltonian/LiftedCompact.lean (declaration OAI.PackingSufficiencySupport.Hamiltonian.exists_scaled_slice_rearrangement)

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
open scoped ContDiff Topology
open Set Function
open Comparison
open scoped BigOperators
open MeasureTheory
section

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_scaled_slice_rearrangement_bp240 {Y : Set P} (hY : IsCompact Y)
    {L : P → ℝ} (hL : Continuous L) (hcL : ConcaveOn ℝ Y L)
    (F : C(P × ℝ,ℝ))
    (hconv : ∀ y ∈ Y, ConvexOn ℝ (Icc 0 (L y)) (fun v => F (y,v)))
    {ε : ℝ} (he : 0 < ε) :
    ∃ (a χ : P → ℝ) (Ψ : HamiltonianDiskIsotopyFamily P (areaRadius 1)),
      ContDiff ℝ ∞ a ∧ (∀ y, 0 < a y) ∧ ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ y, χ y ∈ Icc 0 1) ∧
      (∀ y ∈ tsupport χ, (a y)^2 < L y) ∧
      (∀ y ∈ Y, ∀ t x, radialArea x ≤ L y →
        radialArea (scaledPlanarTrace Ψ.motion a χ y t x) ≤ L y) ∧
      (∀ y ∈ Y, ∀ x, radialArea x ≤ L y →
        F (y,radialArea (scaledPlanarTrace Ψ.motion a χ y 1 x)) ≤
          intervalMinimum (fiberFunction F y) (L y) (radialArea x)+ε) := by
  sorry

end

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end
