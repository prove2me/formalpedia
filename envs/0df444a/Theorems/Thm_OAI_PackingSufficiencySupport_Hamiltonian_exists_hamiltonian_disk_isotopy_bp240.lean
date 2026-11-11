-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_exists_hamiltonian_disk_isotopy_bp240
-- name    : OAI.PackingSufficiencySupport.Hamiltonian.exists_hamiltonian_disk_isotopy_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:55:51.938204+00:00
-- url     : https://prove2.me/theorems/bb2c12cf-66dd-4c52-bb18-02047c3a2b0f
-- title:
--   OAI.PackingSufficiencySupport.Hamiltonian.exists_hamiltonian_disk_isotopy_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.Hamiltonian.exists_hamiltonian_disk_isotopy` of [lean/OAI/Geometry/BallPacking/DiskMaps/ParameterRelativeDiskMoser.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/DiskMaps/ParameterRelativeDiskMoser.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.Hamiltonian`, with `open scoped ContDiff Topology`, `open Set Function MeasureTheory`):
--
--   ```lean
--   theorem exists_hamiltonian_disk_isotopy_bp240
--       {ι : Type*} [Fintype ι] {R : ℝ} (hR : 0 < R)
--       (Φ : SupportedSmoothIsotopyFamily P Plane (roundDisk R))
--       (Y : Set P) (hY : IsCompact Y)
--       (r : ι → ℝ) (hr : ∀ i, 0 < r i) (hrR : ∀ i, r i < R) (hri : Injective r)
--       (harea : ∀ i y, y ∈ Y → volume (Φ.map y 1 '' closedRoundDisk (r i)) =
--         volume (closedRoundDisk (r i))) :
--       ∃ Ψ : HamiltonianDiskIsotopyFamily P R, ∀ i y, y ∈ Y →
--         Ψ.isotopy.map y 1 '' closedRoundDisk (r i) = Φ.map y 1 '' closedRoundDisk (r i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.Hamiltonian.Plane`, `OAI.PackingSufficiencySupport.Hamiltonian.SupportedSmoothIsotopyFamily` and `OAI.PackingSufficiencySupport.Hamiltonian.roundDisk` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.closedRoundDisk` (definitions bundle `OAIQ240Bp005` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.HamiltonianDiskIsotopyFamily` (definitions bundle `OAIQ240Bp010` of this split).
--
--   **Used by.** The proofs of `OAI.PackingSufficiencySupport.Hamiltonian.exists_scaled_slice_rearrangement_bp240` and `OAI.PackingSufficiencySupport.Hamiltonian.exists_thin_planar_embedding_bp240` of this split import it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/DiskMaps/ParameterRelativeDiskMoser.lean (declaration OAI.PackingSufficiencySupport.Hamiltonian.exists_hamiltonian_disk_isotopy)

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

section
open scoped ContDiff Topology
open Set Function MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

variable [FiniteDimensional ℝ P]

theorem exists_hamiltonian_disk_isotopy_bp240
    {ι : Type*} [Fintype ι] {R : ℝ} (hR : 0 < R)
    (Φ : SupportedSmoothIsotopyFamily P Plane (roundDisk R))
    (Y : Set P) (hY : IsCompact Y)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (hrR : ∀ i, r i < R) (hri : Injective r)
    (harea : ∀ i y, y ∈ Y → volume (Φ.map y 1 '' closedRoundDisk (r i)) =
      volume (closedRoundDisk (r i))) :
    ∃ Ψ : HamiltonianDiskIsotopyFamily P R, ∀ i y, y ∈ Y →
      Ψ.isotopy.map y 1 '' closedRoundDisk (r i) = Φ.map y 1 '' closedRoundDisk (r i) := by
  sorry

end

open scoped ContDiff Topology
open Set Function

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end
