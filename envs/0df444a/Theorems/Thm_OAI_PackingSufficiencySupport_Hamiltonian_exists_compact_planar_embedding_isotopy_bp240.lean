-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_exists_compact_planar_embedding_isotopy_bp240
-- name    : OAI.PackingSufficiencySupport.Hamiltonian.exists_compact_planar_embedding_isotopy_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:06:13.838364+00:00
-- url     : https://prove2.me/theorems/6b646deb-3a4e-447f-b314-e0c4d2b42c18
-- title:
--   OAI.PackingSufficiencySupport.Hamiltonian.exists_compact_planar_embedding_isotopy_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.Hamiltonian.exists_compact_planar_embedding_isotopy` of [lean/OAI/Geometry/BallPacking/DiskMaps/CompactEmbeddingIsotopy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/DiskMaps/CompactEmbeddingIsotopy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.Hamiltonian`, with `open scoped ContDiff Topology`, `open Set Function`, `open MeasureTheory`):
--
--   ```lean
--   theorem exists_compact_planar_embedding_isotopy_bp240
--       (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f)
--       (U W : Set ℂ) (hU : IsOpen U) (hW : IsOpen W)
--       (hcU : Convex ℝ U) (hcW : Convex ℝ W)
--       (hinj : InjOn f U) (hi : ∀ x ∈ U, (fderiv ℝ f x).IsInvertible)
--       (K : Set ℂ) (hK : IsCompact K) (h0K : (0:ℂ) ∈ K)
--       (hKU : K ⊆ U) (hKW : K ⊆ W) (hfKW : MapsTo f K W)
--       (hor : 0 < (fderiv ℝ f 0 1).re * (fderiv ℝ f 0 Complex.I).im -
--         (fderiv ℝ f 0 1).im * (fderiv ℝ f 0 Complex.I).re) :
--       SmoothlyAmbientRelated W K id f
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.Hamiltonian.SmoothlyAmbientRelated` (definitions bundle `OAIQ240Bp007` of this split).
--
--   **Used by.** The proof of `OAI.PackingSufficiencySupport.Hamiltonian.exists_hamiltonian_disk_germs_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/DiskMaps/CompactEmbeddingIsotopy.lean (declaration OAI.PackingSufficiencySupport.Hamiltonian.exists_compact_planar_embedding_isotopy)

import Mathlib
import Definitions.Def_OAIQ240Bp007

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
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [CompleteSpace E] [FiniteDimensional ℝ E]

theorem exists_compact_planar_embedding_isotopy_bp240
    (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f)
    (U W : Set ℂ) (hU : IsOpen U) (hW : IsOpen W)
    (hcU : Convex ℝ U) (hcW : Convex ℝ W)
    (hinj : InjOn f U) (hi : ∀ x ∈ U, (fderiv ℝ f x).IsInvertible)
    (K : Set ℂ) (hK : IsCompact K) (h0K : (0:ℂ) ∈ K)
    (hKU : K ⊆ U) (hKW : K ⊆ W) (hfKW : MapsTo f K W)
    (hor : 0 < (fderiv ℝ f 0 1).re * (fderiv ℝ f 0 Complex.I).im -
      (fderiv ℝ f 0 1).im * (fderiv ℝ f 0 Complex.I).re) :
    SmoothlyAmbientRelated W K id f := by
  sorry

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end
