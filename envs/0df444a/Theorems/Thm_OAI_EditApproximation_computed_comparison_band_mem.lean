-- Prove2me | Theorems.Thm_OAI_EditApproximation_computed_comparison_band_mem
-- name    : OAI.EditApproximation.computed_comparison_band_mem
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T17:23:20.709862+00:00
-- url     : https://prove2.me/theorems/78580df6-7829-430a-a5d8-66aff870dd8e
-- title:
--   OAI.EditApproximation.computed_comparison_band_mem: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.computed_comparison_band_mem` of [lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedComparisonBand.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedComparisonBand.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open Finset`):
--
--   ```lean
--   theorem computed_comparison_band_mem {α : Type*} (source target : List α)
--       (N : ℕ) (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N)
--       {M b P : ℕ} (hM : 0 < M) (hMeq : M = (integerParameters N).M)
--       (parent : TargetInterval source.length) (r : TargetInterval target.length)
--       (comparison : Fin M → TargetInterval target.length)
--       (hcomparison : comparison ∈ wideActionList M parent r b P)
--       (hnonempty : wideActionList M parent r b P ≠ [])
--       (child : Fin M → TargetInterval target.length → ℚ) (a : ℝ) (ha : 1 ≤ a)
--       (hchild : ∀ i s, max ((stateEditCost
--         (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s : ℝ) / a)
--           |stateLengthGap (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s| ≤
--             (child i s : ℝ))
--       (hupper : ∀ i, (child i (comparison i) : ℝ) ≤ 2 * inputSmallLog N * stateEditCost
--         (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (comparison i))
--       (hcostSum : (∑ i, (stateEditCost
--         (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (comparison i) : ℝ)) ≤ 4 * b)
--       (hpositive : 0 < stateEditCost (substring source parent.lo parent.hi) target r)
--       (hzero : endpointActionConnection r comparison = 0)
--       (hanchors : ∀ i, Nat.dist (r.lo + ((sourceChild parent i).lo - parent.lo)) (comparison i).lo ≤ 6 * b ∧
--         Nat.dist (r.lo + ((sourceChild parent i).hi - parent.lo)) (comparison i).hi ≤ 6 * b)
--       (hvelocity : |rationalStateGap (substring source parent.lo parent.hi) target r /
--         rationalWideActionMinimum parent r b P hnonempty child| ≤
--           1 - (rationalParameters (inputSmallLog N)).tau)
--       (hKsmall : comparisonActionCurvature source target parent r comparison (fun i s => (child i s : ℝ)) ≤
--         b / heightQuarterRoot N)
--       (hGsmall : comparisonActionMass comparison (fun i s => (child i s : ℝ)) -
--         wideActionMinimum parent r b P hnonempty (fun i s => (child i s : ℝ)) ≤ b / heightQuarterRoot N) :
--       comparison ∈ representativeBandActions source target parent r b P
--         (rationalParameters (inputSmallLog N)).tau (rationalParameters (inputSmallLog N)).theta child
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.comparisonActionCurvature`, `OAI.EditApproximation.comparisonActionMass`, `OAI.EditApproximation.heightQuarterRoot`, `OAI.EditApproximation.stateEditCost`, `OAI.EditApproximation.stateLengthGap` and `OAI.EditApproximation.wideActionMinimum` (definitions bundle `OAIQ361V3Ea001` of this split); `OAI.EditApproximation.inputSmallLog`, `OAI.EditApproximation.integerParameters`, `OAI.EditApproximation.rationalParameters`, `OAI.EditApproximation.IntegerParameters` and `OAI.EditApproximation.RationalParameters` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.TargetInterval` and `OAI.EditApproximation.substring` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.rationalStateGap`, `OAI.EditApproximation.sourceChild` and `OAI.EditApproximation.wideActionList` (the published bundle `Def_EditApproxScheme_06`); `OAI.EditApproximation.endpointActionConnection` (the published bundle `Def_EditApproxScheme_09`); `OAI.EditApproximation.rationalWideActionMinimum` and `OAI.EditApproximation.representativeBandActions` (the published bundle `Def_EditApproxScheme_10`).
--
--   **Used by.** The proofs of `OAI.EditApproximation.physicalProgram_comparison_node_regret` and `OAI.EditApproximation.physicalProgram_subtree_node_regret` of this split import it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedComparisonBand.lean (declaration OAI.EditApproximation.computed_comparison_band_mem)

import Mathlib
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_OAIQ361V3Ea001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

open Finset

theorem computed_comparison_band_mem {α : Type*} (source target : List α)
    (N : ℕ) (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N)
    {M b P : ℕ} (hM : 0 < M) (hMeq : M = (integerParameters N).M)
    (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (comparison : Fin M → TargetInterval target.length)
    (hcomparison : comparison ∈ wideActionList M parent r b P)
    (hnonempty : wideActionList M parent r b P ≠ [])
    (child : Fin M → TargetInterval target.length → ℚ) (a : ℝ) (ha : 1 ≤ a)
    (hchild : ∀ i s, max ((stateEditCost
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s : ℝ) / a)
        |stateLengthGap (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s| ≤
          (child i s : ℝ))
    (hupper : ∀ i, (child i (comparison i) : ℝ) ≤ 2 * inputSmallLog N * stateEditCost
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (comparison i))
    (hcostSum : (∑ i, (stateEditCost
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (comparison i) : ℝ)) ≤ 4 * b)
    (hpositive : 0 < stateEditCost (substring source parent.lo parent.hi) target r)
    (hzero : endpointActionConnection r comparison = 0)
    (hanchors : ∀ i, Nat.dist (r.lo + ((sourceChild parent i).lo - parent.lo)) (comparison i).lo ≤ 6 * b ∧
      Nat.dist (r.lo + ((sourceChild parent i).hi - parent.lo)) (comparison i).hi ≤ 6 * b)
    (hvelocity : |rationalStateGap (substring source parent.lo parent.hi) target r /
      rationalWideActionMinimum parent r b P hnonempty child| ≤
        1 - (rationalParameters (inputSmallLog N)).tau)
    (hKsmall : comparisonActionCurvature source target parent r comparison (fun i s => (child i s : ℝ)) ≤
      b / heightQuarterRoot N)
    (hGsmall : comparisonActionMass comparison (fun i s => (child i s : ℝ)) -
      wideActionMinimum parent r b P hnonempty (fun i s => (child i s : ℝ)) ≤ b / heightQuarterRoot N) :
    comparison ∈ representativeBandActions source target parent r b P
      (rationalParameters (inputSmallLog N)).tau (rationalParameters (inputSmallLog N)).theta child := by
  sorry

end EditApproximation

end OAI
end
