-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_DiagonalQuadrics_exists_quadric_exact_affine_moser_bp240
-- name    : OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_quadric_exact_affine_moser_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:52:43.911+00:00
-- url     : https://prove2.me/theorems/09fe9b26-c618-435c-836c-758ecf8e7923
-- title:
--   OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_quadric_exact_affine_moser_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_quadric_exact_affine_moser` of [lean/OAI/Geometry/BallPacking/BallMaps/QuadricRelativeShellFlow.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallMaps/QuadricRelativeShellFlow.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.DiagonalQuadrics`, with `open scoped ContDiff`, `open Function`, `open Hamiltonian`, `open scoped Manifold Topology`, `open Set`):
--
--   ```lean
--    theorem exists_quadric_exact_affine_moser_bp240 {m : ℕ} (a : Fin m → ℂ) (t : ℝ)
--       {c d : ℝ} (hc : 0 < c) (hd : 0≤d) (hdhalf : d<1/2) :
--       ∃ g h : Affine m → Affine m,∃ f : Affine m → ℝ,
--         ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ h ∧ ContDiff ℝ ∞ f ∧
--         LeftInverse h g ∧ RightInverse h g ∧
--         ∀ x,primitivePullback (ambientFSPrimitive c) g x=
--           normalAmbientPrimitive a c d t x+fderiv ℝ f x
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.DiagonalQuadrics.Affine` and `OAI.PackingSufficiencySupport.Hamiltonian.primitivePullback` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.DiagonalQuadrics.ambientFSPrimitive` and `OAI.PackingSufficiencySupport.DiagonalQuadrics.normalAmbientPrimitive` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proof of `OAI.PackingSufficiencySupport.actual_complement_packing_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallMaps/QuadricRelativeShellFlow.lean (declaration OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_quadric_exact_affine_moser)

import Mathlib
import Definitions.Def_OAIQ240Bp019

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
open Function
open Hamiltonian
open scoped Manifold Topology
open Set

 theorem exists_quadric_exact_affine_moser_bp240 {m : ℕ} (a : Fin m → ℂ) (t : ℝ)
    {c d : ℝ} (hc : 0 < c) (hd : 0≤d) (hdhalf : d<1/2) :
    ∃ g h : Affine m → Affine m,∃ f : Affine m → ℝ,
      ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ h ∧ ContDiff ℝ ∞ f ∧
      LeftInverse h g ∧ RightInverse h g ∧
      ∀ x,primitivePullback (ambientFSPrimitive c) g x=
        normalAmbientPrimitive a c d t x+fderiv ℝ f x := by
  sorry

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end
