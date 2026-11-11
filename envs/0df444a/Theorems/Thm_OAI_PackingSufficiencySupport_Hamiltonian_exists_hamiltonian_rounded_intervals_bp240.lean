-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_exists_hamiltonian_rounded_intervals_bp240
-- name    : OAI.PackingSufficiencySupport.Hamiltonian.exists_hamiltonian_rounded_intervals_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:06:34.266664+00:00
-- url     : https://prove2.me/theorems/9acdf77e-f32a-409d-a8a2-c527168ffed1
-- title:
--   OAI.PackingSufficiencySupport.Hamiltonian.exists_hamiltonian_rounded_intervals_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.Hamiltonian.exists_hamiltonian_rounded_intervals` of [lean/OAI/Geometry/BallPacking/Hamiltonian/CartesianMomentSlices.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Hamiltonian/CartesianMomentSlices.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.Hamiltonian`, with `open scoped ContDiff Topology`, `open Set Function MeasureTheory`, `open Comparison`):
--
--   ```lean
--   theorem exists_hamiltonian_rounded_intervals_bp240 {m : ℕ} {Y : Set P}
--       (hY : IsCompact Y) (hcY : Convex ℝ Y) (y₀ : P) (hy₀ : y₀ ∈ Y)
--       (h L w : Fin m → ℝ) (hh : ∀ i, 0 < h i) (hh1 : ∀ i, h i < 1)
--       (hhmono : StrictMono h) (hw : ∀ i, 0 < w i) (hw1 : ∀ i, w i < 1)
--       (hwmono : StrictMono w) (hL : ∀ i, L i*w i = h i)
--       (c : P → Fin m → ℝ) (hc : ContDiff ℝ ∞ c)
--       (V : P → Fin m → Set ℝ)
--       (hV : ∀ i, IsOpen {p : P × ℝ | p.2 ∈ V p.1 i})
--       (hVconv : ∀ y ∈ Y, ∀ i, Convex ℝ (V y i))
--       (hVsub : ∀ y i, V y i ⊆ Ioo 0 1)
--       (hplace : ∀ y ∈ Y, (∀ i, c y i ∈ V y i ∧ c y i+L i ∈ V y i) ∧
--         StrictNestedStarts L (c y)) :
--       ∃ Ψ : HamiltonianDiskIsotopyFamily P (areaRadius 1),
--         ∀ i y, y ∈ Y → ∀ x ∈ closedRoundDisk (areaRadius (h i)),
--           radialArea (Ψ.isotopy.map y 1 x) ∈ V y i
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.Hamiltonian.Plane`, `OAI.PackingSufficiencySupport.Hamiltonian.roundDisk` and `OAI.PackingSufficiencySupport.Hamiltonian.SupportedSmoothIsotopyFamily` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.StrictNestedStarts` and `OAI.PackingSufficiencySupport.Hamiltonian.areaRadius` (definitions bundle `OAIQ240Bp004` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.closedRoundDisk` (definitions bundle `OAIQ240Bp005` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.HamiltonianDiskIsotopyFamily` and `OAI.PackingSufficiencySupport.Hamiltonian.radialArea` (definitions bundle `OAIQ240Bp010` of this split).
--
--   **Used by.** The proof of `OAI.PackingSufficiencySupport.Hamiltonian.exists_scaled_slice_rearrangement_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Hamiltonian/CartesianMomentSlices.lean (declaration OAI.PackingSufficiencySupport.Hamiltonian.exists_hamiltonian_rounded_intervals)

import Mathlib
import Definitions.Def_OAIQ240Bp010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function MeasureTheory
open Comparison
section

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_hamiltonian_rounded_intervals_bp240 {m : ℕ} {Y : Set P}
    (hY : IsCompact Y) (hcY : Convex ℝ Y) (y₀ : P) (hy₀ : y₀ ∈ Y)
    (h L w : Fin m → ℝ) (hh : ∀ i, 0 < h i) (hh1 : ∀ i, h i < 1)
    (hhmono : StrictMono h) (hw : ∀ i, 0 < w i) (hw1 : ∀ i, w i < 1)
    (hwmono : StrictMono w) (hL : ∀ i, L i*w i = h i)
    (c : P → Fin m → ℝ) (hc : ContDiff ℝ ∞ c)
    (V : P → Fin m → Set ℝ)
    (hV : ∀ i, IsOpen {p : P × ℝ | p.2 ∈ V p.1 i})
    (hVconv : ∀ y ∈ Y, ∀ i, Convex ℝ (V y i))
    (hVsub : ∀ y i, V y i ⊆ Ioo 0 1)
    (hplace : ∀ y ∈ Y, (∀ i, c y i ∈ V y i ∧ c y i+L i ∈ V y i) ∧
      StrictNestedStarts L (c y)) :
    ∃ Ψ : HamiltonianDiskIsotopyFamily P (areaRadius 1),
      ∀ i y, y ∈ Y → ∀ x ∈ closedRoundDisk (areaRadius (h i)),
        radialArea (Ψ.isotopy.map y 1 x) ∈ V y i := by
  sorry

end

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end
