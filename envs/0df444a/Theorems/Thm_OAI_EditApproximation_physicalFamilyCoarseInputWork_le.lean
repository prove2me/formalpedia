-- Prove2me | Theorems.Thm_OAI_EditApproximation_physicalFamilyCoarseInputWork_le
-- name    : OAI.EditApproximation.physicalFamilyCoarseInputWork_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:33:41.93169+00:00
-- url     : https://prove2.me/theorems/cf73e136-84e9-4fdb-a98a-4f375a0fea1d
-- title:
--   OAI.EditApproximation.physicalFamilyCoarseInputWork_le: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.physicalFamilyCoarseInputWork_le` of [lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalCoarseInputWork.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalCoarseInputWork.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`):
--
--   ```lean
--   theorem physicalFamilyCoarseInputWork_le (bits : ℕ) (encode : Sum Key Table → ℕ)
--       (hinjective : Function.Injective encode) (hbounded : ∀ key, encode key < 2 ^ bits)
--       (root : Table) (hroot : root.depth = J) :
--       physicalFamilyCoarseInputWork source target N P H T S passes copies factor multiplier
--         tau eta kappa delta initial draw bits encode root ≤
--       ((physicalFamilyDependencyTree source target N P H T S passes copies factor multiplier
--         tau eta kappa delta initial hP draw root).widthWork M source.length : ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.DependencyExpansion.widthWork` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.physicalFamilyCoarseInputWork` and `OAI.EditApproximation.physicalFamilyDependencyTree` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.inputSmallLog` and `OAI.EditApproximation.smallLogExponent` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.PhysicalEntry` (the published bundle `Def_EditApproxScheme_06`); `OAI.EditApproximation.ChargedPhysicalRequest` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.ChargedPhysicalRequest.depth` (the published bundle `Def_EditApproxScheme_11`); `OAI.EditApproximation.PhysicalFamilyScalarDraw` and `OAI.EditApproximation.PhysicalFamilyScalarKey` (the published bundle `Def_EditApproxScheme_14`).
--
--   **Used by.** The proof of `OAI.EditApproximation.computedFamilyCoarseInputWork_le` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalCoarseInputWork.lean (declaration OAI.EditApproximation.physicalFamilyCoarseInputWork_le)

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.Integration
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_11
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

section Coarse
variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (initial : PhysicalEntry M J target.length → ℕ) (hP : 0 < P)
  (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P (inputSmallLog N) (40 * smallLogExponent N) H (inputSmallLog N ^ 80) passes copies)

local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "Key" => PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "Table" => ChargedPhysicalRequest M J target.length (passes + 1) copies T S
local notation "readGroup" => physicalFamilyGroupRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "readInteger" => physicalFamilyOnlineRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "answer" => physicalFamilyAnswer target N P ell exponent H (ell ^ 80) passes copies draw

theorem physicalFamilyCoarseInputWork_le (bits : ℕ) (encode : Sum Key Table → ℕ)
    (hinjective : Function.Injective encode) (hbounded : ∀ key, encode key < 2 ^ bits)
    (root : Table) (hroot : root.depth = J) :
    physicalFamilyCoarseInputWork source target N P H T S passes copies factor multiplier
      tau eta kappa delta initial draw bits encode root ≤
    ((physicalFamilyDependencyTree source target N P H T S passes copies factor multiplier
      tau eta kappa delta initial hP draw root).widthWork M source.length : ℝ) := by
  sorry

end Coarse
end EditApproximation

end OAI
end
