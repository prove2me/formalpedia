-- Prove2me | Theorems.Thm_OAI_EditApproximation_physicalFamilyMemoCoarseWork_expected_le
-- name    : OAI.EditApproximation.physicalFamilyMemoCoarseWork_expected_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:36:46.681481+00:00
-- url     : https://prove2.me/theorems/e60f55e1-bba9-46e4-ad02-10e2b4f79b1a
-- title:
--   OAI.EditApproximation.physicalFamilyMemoCoarseWork_expected_le: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.physicalFamilyMemoCoarseWork_expected_le` of [lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalFamilyMemoCoarse.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalFamilyMemoCoarse.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open MeasureTheory`):
--
--   ```lean
--    theorem physicalFamilyMemoCoarseWork_expected_le (hP : 0 < P) (hN : 0 < N)
--       (hell : 200 ≤ ell) (hB : B = (integerParameters N).B)
--       (hsize : source.length + target.length ≤ N)
--       (hdepth : ∀ entry, depth entry = computedCoarseDepth N
--         (coarseEntryWidth (physicalSource source entry.1) (substring target entry.2.lo entry.2.hi)))
--       (hinverse : coarseInverseAllowanceFactor B (initialThresholdQ N) (initialLambda N) ≤
--         (inputHeight N : ℝ) ^ 8)
--       (bits : ℕ) (encode : Sum Key Table → ℕ) (hinjective : Function.Injective encode)
--       (hbounded : ∀ key, encode key < 2 ^ bits) (root : Table) (hroot : root.depth = J)
--       (budget : ℝ)
--       (hwidth : ∀ coarse : PhysicalCoarseDraw source target B depth,
--         ((physicalFamilyDependencyTree source target N P H T S passes copies factor multiplier
--           tau eta kappa delta (clampedSeedNat (physicalCoarseSeedTable source target N B depth coarse))
--           hP draw root).widthWork M source.length : ℝ) ≤ budget) :
--       (∫ coarse, physicalFamilyMemoCoarseWork source target N P H T S passes copies factor multiplier
--         tau eta kappa delta draw B depth bits encode root coarse
--         ∂coarseFullSeedMeasure B depth
--           (fun entry => physicalSource source entry.1)
--           (fun entry => substring target entry.2.lo entry.2.hi)) ≤
--       budget * computedCoarseWidthOverhead N
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.DependencyExpansion.widthWork` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.coarseInverseAllowanceFactor` and `OAI.EditApproximation.computedCoarseWidthOverhead` (definitions bundle `OAIQ361V3Ea001` of this split); `OAI.EditApproximation.physicalFamilyDependencyTree` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.initialLambda`, `OAI.EditApproximation.initialThresholdQ`, `OAI.EditApproximation.inputHeight`, `OAI.EditApproximation.inputSmallLog`, `OAI.EditApproximation.integerParameters`, `OAI.EditApproximation.smallLogExponent` and `OAI.EditApproximation.IntegerParameters` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.CoarseThresholdDraws`, `OAI.EditApproximation.PhysicalNode`, `OAI.EditApproximation.computedCoarseDepth` and `OAI.EditApproximation.physicalNodeFintype` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.TargetInterval` and `OAI.EditApproximation.substring` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.PhysicalEntry` and `OAI.EditApproximation.physicalSource` (the published bundle `Def_EditApproxScheme_06`); `OAI.EditApproximation.ChargedPhysicalRequest` and `OAI.EditApproximation.coarseDrawsMeasurableSpace` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.clampedSeedNat` (the published bundle `Def_EditApproxScheme_10`); `OAI.EditApproximation.CoarseFullSeedDraws`, `OAI.EditApproximation.CoarseGuessIndex`, `OAI.EditApproximation.coarseEntryWidth`, `OAI.EditApproximation.coarseFullSeedMeasure` and `OAI.EditApproximation.ChargedPhysicalRequest.depth` (the published bundle `Def_EditApproxScheme_11`); `OAI.EditApproximation.targetIntervalFintype` (the published bundle `Def_EditApproxScheme_13`); `OAI.EditApproximation.PhysicalFamilyScalarDraw` and `OAI.EditApproximation.PhysicalFamilyScalarKey` (the published bundle `Def_EditApproxScheme_14`); `OAI.EditApproximation.PhysicalCoarseDraw` and `OAI.EditApproximation.physicalCoarseSeedTable` (the published bundle `Def_EditApproxScheme_15`); `OAI.EditApproximation.physicalFamilyMemoCoarseWork` (the published bundle `Def_EditApproxScheme_16`).
--
--   **Used by.** The proof of `OAI.EditApproximation.computedPhysicalCoarseWork_expected_le` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/PhysicalFamilyMemoCoarse.lean (declaration OAI.EditApproximation.physicalFamilyMemoCoarseWork_expected_le)

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.Integration
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_EditApproxScheme_16
import Definitions.Def_OAIQ361V3Ea002

section

attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

open MeasureTheory

section Coarse

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P (inputSmallLog N) (40 * smallLogExponent N) H (inputSmallLog N ^ 80) passes copies)
  (B : ℕ) [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
  (depth : PhysicalEntry M J target.length → ℕ)

local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "Key" => PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "Table" => ChargedPhysicalRequest M J target.length (passes + 1) copies T S

 theorem physicalFamilyMemoCoarseWork_expected_le (hP : 0 < P) (hN : 0 < N)
    (hell : 200 ≤ ell) (hB : B = (integerParameters N).B)
    (hsize : source.length + target.length ≤ N)
    (hdepth : ∀ entry, depth entry = computedCoarseDepth N
      (coarseEntryWidth (physicalSource source entry.1) (substring target entry.2.lo entry.2.hi)))
    (hinverse : coarseInverseAllowanceFactor B (initialThresholdQ N) (initialLambda N) ≤
      (inputHeight N : ℝ) ^ 8)
    (bits : ℕ) (encode : Sum Key Table → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (root : Table) (hroot : root.depth = J)
    (budget : ℝ)
    (hwidth : ∀ coarse : PhysicalCoarseDraw source target B depth,
      ((physicalFamilyDependencyTree source target N P H T S passes copies factor multiplier
        tau eta kappa delta (clampedSeedNat (physicalCoarseSeedTable source target N B depth coarse))
        hP draw root).widthWork M source.length : ℝ) ≤ budget) :
    (∫ coarse, physicalFamilyMemoCoarseWork source target N P H T S passes copies factor multiplier
      tau eta kappa delta draw B depth bits encode root coarse
      ∂coarseFullSeedMeasure B depth
        (fun entry => physicalSource source entry.1)
        (fun entry => substring target entry.2.lo entry.2.hi)) ≤
    budget * computedCoarseWidthOverhead N := by
  sorry

end Coarse

end EditApproximation

end OAI
end
