-- Prove2me | Theorems.Thm_OAI_EditApproximation_physicalFamilyDependencyTree_valid
-- name    : OAI.EditApproximation.physicalFamilyDependencyTree_valid
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:23:56.677841+00:00
-- url     : https://prove2.me/theorems/dee4a138-5ffe-450f-b359-e9dd639e769e
-- title:
--   OAI.EditApproximation.physicalFamilyDependencyTree_valid: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.physicalFamilyDependencyTree_valid` of [lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalFamilyWork.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalFamilyWork.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`):
--
--   ```lean
--    theorem physicalFamilyDependencyTree_valid
--       (hN : 0 < N) (hell : 200 ≤ ell) (hM : M = (integerParameters N).M)
--       (hP : P = (integerParameters N).P) (hT : T = (integerParameters N).T)
--       (hS : S = (integerParameters N).S) (hcopies : copies ≤ inputHeight N ^ 2)
--       (hAmin : ∀ pass, 1 ≤ factor pass)
--       (hAmax : ∀ pass, factor pass ≤ ((integerParameters N).initialFactor : ℚ))
--       (root : ChargedPhysicalRequest M J target.length (passes + 1) copies T S) :
--       (physicalFamilyDependencyTree source target N P H T S passes copies factor multiplier
--         tau eta kappa delta initial hPpos draw root).Valid
--         (M * ell ^ 257) (inputHeight N ^ (512 * (coarseExponent ell + 1)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.physicalFamilyDependencyTree` and `OAI.EditApproximation.DependencyExpansion.Valid` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.coarseExponent`, `OAI.EditApproximation.inputHeight`, `OAI.EditApproximation.inputSmallLog`, `OAI.EditApproximation.integerParameters`, `OAI.EditApproximation.smallLogExponent` and `OAI.EditApproximation.IntegerParameters` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.PhysicalEntry` (the published bundle `Def_EditApproxScheme_06`); `OAI.EditApproximation.ChargedPhysicalRequest` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.PhysicalFamilyScalarDraw` (the published bundle `Def_EditApproxScheme_14`).
--
--   **Used by.** The proof of `OAI.EditApproximation.computedPhysicalCoarseWork_expected_le` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalFamilyWork.lean (declaration OAI.EditApproximation.physicalFamilyDependencyTree_valid)

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea002

section

attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Work

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (initial : PhysicalEntry M J target.length → ℕ) (hPpos : 0 < P)
  (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P (inputSmallLog N) (40 * smallLogExponent N) H (inputSmallLog N ^ 80) passes copies)

local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "group" => physicalFamilyGroup target N P ell exponent H (ell ^ 80) passes copies draw
local notation "integer" => physicalFamilyInteger source target N P ell exponent H (ell ^ 80)
  T S passes copies factor multiplier tau eta kappa delta hPpos draw initial
local notation "readGroup" => physicalFamilyGroupRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "readInteger" => physicalFamilyOnlineRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "answer" => physicalFamilyAnswer target N P ell exponent H (ell ^ 80) passes copies draw
local notation "bodyValue" => physicalFamilyProgram_value source target N P ell exponent H (ell ^ 80)
  T S passes copies factor multiplier tau eta kappa delta initial hPpos draw

 theorem physicalFamilyDependencyTree_valid
    (hN : 0 < N) (hell : 200 ≤ ell) (hM : M = (integerParameters N).M)
    (hP : P = (integerParameters N).P) (hT : T = (integerParameters N).T)
    (hS : S = (integerParameters N).S) (hcopies : copies ≤ inputHeight N ^ 2)
    (hAmin : ∀ pass, 1 ≤ factor pass)
    (hAmax : ∀ pass, factor pass ≤ ((integerParameters N).initialFactor : ℚ))
    (root : ChargedPhysicalRequest M J target.length (passes + 1) copies T S) :
    (physicalFamilyDependencyTree source target N P H T S passes copies factor multiplier
      tau eta kappa delta initial hPpos draw root).Valid
      (M * ell ^ 257) (inputHeight N ^ (512 * (coarseExponent ell + 1))) := by
  sorry

end Work

end EditApproximation

end OAI
end
