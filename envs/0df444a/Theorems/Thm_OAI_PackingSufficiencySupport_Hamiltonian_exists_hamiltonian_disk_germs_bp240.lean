-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_exists_hamiltonian_disk_germs_bp240
-- name    : OAI.PackingSufficiencySupport.Hamiltonian.exists_hamiltonian_disk_germs_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:11:10.997347+00:00
-- url     : https://prove2.me/theorems/228d6fc5-335e-45b7-b85e-871c02f782d9
-- title:
--   OAI.PackingSufficiencySupport.Hamiltonian.exists_hamiltonian_disk_germs_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.Hamiltonian.exists_hamiltonian_disk_germs` of [lean/OAI/Geometry/BallPacking/Layers/ParametricNestedDisks.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Layers/ParametricNestedDisks.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.Hamiltonian`, with `open scoped ContDiff Topology`, `open Set Function`, `open MeasureTheory`, `open Metric`):
--
--   ```lean
--   theorem exists_hamiltonian_disk_germs_bp240 {m : ℕ} {Y A : Set P}
--       (hY : IsCompact Y) (hcY : Convex ℝ Y) (hA : IsOpen A) (hYA : Y ⊆ A)
--       (y₀ : P) (hy₀ : y₀ ∈ Y) (r : Fin m → ℝ) (hr : ∀ i, 0 < r i)
--       (hrmono : StrictMono r) (f : Fin m → P × ℂ → ℂ)
--       (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (A ×ˢ univ))
--       (hi : ∀ i y, y ∈ A → Injective (fun x => f i (y,x)))
--       (hd : ∀ i y, y ∈ A → ∀ x, (fderiv ℝ (fun x => f i (y,x)) x).IsInvertible)
--       (ho : ∀ i y, y ∈ A → 0 < (fderiv ℝ (fun x => f i (y,x)) 0).det)
--       (hnest : ∀ ⦃i j⦄, i < j → ∀ y ∈ Y,
--         (fun x => f i (y,x)) '' Metric.closedBall 0 (r i) ⊆
--           interior ((fun x => f j (y,x)) '' Metric.closedBall 0 (r j)))
--       (R : ℝ) (hR : 0 < R) (hrR : ∀ i, r i < R)
--       (hfit : ∀ i y, y ∈ Y →
--         (fun x => f i (y,x)) '' Metric.closedBall 0 (r i) ⊆ Metric.ball 0 R)
--       (harea : ∀ i y, y ∈ Y → volume ((fun x => f i (y,x)) '' Metric.closedBall 0 (r i)) =
--         volume (Metric.closedBall (0:ℂ) (r i))) :
--       ∃ Ψ : HamiltonianDiskIsotopyFamily P R, ∀ i y, y ∈ Y →
--         Ψ.isotopy.map y 1 '' closedRoundDisk (r i) =
--           Complex.equivRealProdCLM '' ((fun x => f i (y,x)) '' Metric.closedBall 0 (r i))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.Hamiltonian.Plane`, `OAI.PackingSufficiencySupport.Hamiltonian.roundDisk` and `OAI.PackingSufficiencySupport.Hamiltonian.SupportedSmoothIsotopyFamily` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.closedRoundDisk` (definitions bundle `OAIQ240Bp005` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.HamiltonianDiskIsotopyFamily` (definitions bundle `OAIQ240Bp010` of this split).
--
--   **Used by.** The proof of `OAI.PackingSufficiencySupport.Hamiltonian.exists_hamiltonian_rounded_intervals_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Layers/ParametricNestedDisks.lean (declaration OAI.PackingSufficiencySupport.Hamiltonian.exists_hamiltonian_disk_germs)

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
open Set Function
open MeasureTheory
open Metric

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_hamiltonian_disk_germs_bp240 {m : ℕ} {Y A : Set P}
    (hY : IsCompact Y) (hcY : Convex ℝ Y) (hA : IsOpen A) (hYA : Y ⊆ A)
    (y₀ : P) (hy₀ : y₀ ∈ Y) (r : Fin m → ℝ) (hr : ∀ i, 0 < r i)
    (hrmono : StrictMono r) (f : Fin m → P × ℂ → ℂ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (A ×ˢ univ))
    (hi : ∀ i y, y ∈ A → Injective (fun x => f i (y,x)))
    (hd : ∀ i y, y ∈ A → ∀ x, (fderiv ℝ (fun x => f i (y,x)) x).IsInvertible)
    (ho : ∀ i y, y ∈ A → 0 < (fderiv ℝ (fun x => f i (y,x)) 0).det)
    (hnest : ∀ ⦃i j⦄, i < j → ∀ y ∈ Y,
      (fun x => f i (y,x)) '' Metric.closedBall 0 (r i) ⊆
        interior ((fun x => f j (y,x)) '' Metric.closedBall 0 (r j)))
    (R : ℝ) (hR : 0 < R) (hrR : ∀ i, r i < R)
    (hfit : ∀ i y, y ∈ Y →
      (fun x => f i (y,x)) '' Metric.closedBall 0 (r i) ⊆ Metric.ball 0 R)
    (harea : ∀ i y, y ∈ Y → volume ((fun x => f i (y,x)) '' Metric.closedBall 0 (r i)) =
      volume (Metric.closedBall (0:ℂ) (r i))) :
    ∃ Ψ : HamiltonianDiskIsotopyFamily P R, ∀ i y, y ∈ Y →
      Ψ.isotopy.map y 1 '' closedRoundDisk (r i) =
        Complex.equivRealProdCLM '' ((fun x => f i (y,x)) '' Metric.closedBall 0 (r i)) := by
  sorry

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end
