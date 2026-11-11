-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_DiagonalQuadrics_exists_quadric_relative_shell_map_bp240
-- name    : OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_quadric_relative_shell_map_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:52:50.396558+00:00
-- url     : https://prove2.me/theorems/a08b711f-3718-4141-a209-573fa072e1c1
-- title:
--   OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_quadric_relative_shell_map_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_quadric_relative_shell_map` of [lean/OAI/Geometry/BallPacking/BallMaps/QuadricRelativeShellFlow.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallMaps/QuadricRelativeShellFlow.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.DiagonalQuadrics`, with `open scoped ContDiff Topology`, `open Set Function`, `open Hamiltonian`):
--
--   ```lean
--   theorem exists_quadric_relative_shell_map_bp240 (a : Fin m → ℂ) (t : ℝ)
--       {c d : ℝ} (hc : 0 < c) (hd : 0≤d) (hdhalf : d<1/2) :
--       ∃ f g : PlanePhase (Option (Option (Fin m))) → PlanePhase (Option (Option (Fin m))),
--         ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ g ∧
--         LeftInverse g f ∧ RightInverse g f ∧
--         (∀ z,phaseSq (f z)=phaseSq z) ∧ (∀ z,phaseSq (g z)=phaseSq z) ∧
--         (∀ ζ : ℂ,∀ hζ : Complex.normSq ζ=1,∀ z,phaseSq z=1 →
--           f (phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) z)=
--             phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) (f z)) ∧
--         (∀ ζ : ℂ,∀ hζ : Complex.normSq ζ=1,∀ z,phaseSq z=1 →
--           g (phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) z)=
--             phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) (g z)) ∧
--         (∀ z,phaseSq z=1 → (complexCartesian.symm (f z) none=0 ↔ complexCartesian.symm z none=0)) ∧
--         (∀ z,phaseSq z=1 → (complexCartesian.symm (g z) none=0 ↔ complexCartesian.symm z none=0)) ∧
--         ∀ z∈phaseShell (1/2:ℝ) 2,∀ v w,
--           euclideanExteriorOneForm (homogeneousConePrimitive (homogeneousCartesian a t) c d) (f z)
--               (fderiv ℝ f z v) (fderiv ℝ f z w)=
--             euclideanExteriorOneForm (homogeneousConePrimitive (homogeneousCartesian a t) c 0) z v w
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.DiagonalQuadrics.NormalPolynomialIndex`, `OAI.PackingSufficiencySupport.Hamiltonian.Plane`, `OAI.PackingSufficiencySupport.Hamiltonian.PlanePhase`, `OAI.PackingSufficiencySupport.Hamiltonian.VeroneseIndex`, `OAI.PackingSufficiencySupport.Hamiltonian.euclideanExteriorOneForm` and `OAI.PackingSufficiencySupport.Hamiltonian.phaseSq` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian` and `OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal` (definitions bundle `OAIQ240Bp010` of this split); `OAI.PackingSufficiencySupport.DiagonalQuadrics.homogeneousCartesian`, `OAI.PackingSufficiencySupport.Hamiltonian.homogeneousConePrimitive` and `OAI.PackingSufficiencySupport.Hamiltonian.phaseShell` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proofs of `OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_polynomial_target_embedding_bp240` and `OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_quadric_exact_affine_moser_bp240` of this split import it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallMaps/QuadricRelativeShellFlow.lean (declaration OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_quadric_relative_shell_map)

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
open scoped ContDiff Topology
open Set Function
open Hamiltonian
section
variable {m : ℕ}

theorem exists_quadric_relative_shell_map_bp240 (a : Fin m → ℂ) (t : ℝ)
    {c d : ℝ} (hc : 0 < c) (hd : 0≤d) (hdhalf : d<1/2) :
    ∃ f g : PlanePhase (Option (Option (Fin m))) → PlanePhase (Option (Option (Fin m))),
      ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ g ∧
      LeftInverse g f ∧ RightInverse g f ∧
      (∀ z,phaseSq (f z)=phaseSq z) ∧ (∀ z,phaseSq (g z)=phaseSq z) ∧
      (∀ ζ : ℂ,∀ hζ : Complex.normSq ζ=1,∀ z,phaseSq z=1 →
        f (phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) z)=
          phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) (f z)) ∧
      (∀ ζ : ℂ,∀ hζ : Complex.normSq ζ=1,∀ z,phaseSq z=1 →
        g (phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) z)=
          phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) (g z)) ∧
      (∀ z,phaseSq z=1 → (complexCartesian.symm (f z) none=0 ↔ complexCartesian.symm z none=0)) ∧
      (∀ z,phaseSq z=1 → (complexCartesian.symm (g z) none=0 ↔ complexCartesian.symm z none=0)) ∧
      ∀ z∈phaseShell (1/2:ℝ) 2,∀ v w,
        euclideanExteriorOneForm (homogeneousConePrimitive (homogeneousCartesian a t) c d) (f z)
            (fderiv ℝ f z v) (fderiv ℝ f z w)=
          euclideanExteriorOneForm (homogeneousConePrimitive (homogeneousCartesian a t) c 0) z v w := by
  sorry

end

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end
