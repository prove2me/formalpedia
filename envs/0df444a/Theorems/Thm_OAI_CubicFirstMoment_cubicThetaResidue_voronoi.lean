-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_cubicThetaResidue_voronoi
-- name    : OAI.CubicFirstMoment.cubicThetaResidue_voronoi
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:38:00.195538+00:00
-- url     : https://prove2.me/theorems/70b72159-f2f5-46a7-b296-987cb8975cf7
-- title:
--   OAI.CubicFirstMoment.cubicThetaResidue_voronoi: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.cubicThetaResidue_voronoi` of [lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaAveragedVoronoi.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaAveragedVoronoi.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open scoped BigOperators MatrixGroups ContDiff`):
--
--   ```lean
--   theorem cubicThetaResidue_voronoi {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
--       [Fintype (Residues r)] (rev : Bool) {k : ℕ} (hk : 0<k)
--       (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
--       (hsm : ContDiff ℝ ∞ W) {σ X : ℝ} (hσ : 0<σ) (hX : 0<X) :
--       Summable (cubicThetaResidueDualTerm r hr rev k W σ X) ∧
--       ((((3^(5/2:ℝ):ℝ):ℂ)*theta (cubicThetaCircleOrder (!rev) k) lambdaE)*
--         ((Real.sqrt (norm r):ℂ)*gauss r))*
--           metaplecticRawCompleted r (cubicThetaCircleOrder (!rev) k) W X=
--       (cubicThetaLevelAngularRoot r rev k)⁻¹*cubicThetaDualPrefactor r*
--         ∑' n,cubicThetaResidueDualTerm r hr rev k W σ X n
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.cubicThetaCircleOrder` (definitions bundle `OAIQ096A003` of this split); `OAI.CubicFirstMoment.MetaplecticDualArgument` and `OAI.CubicFirstMoment.lambdaE` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.gauss` (definitions bundle `OAIQ096A005` of this split); `OAI.CubicFirstMoment.metaplecticRawCompleted` (definitions bundle `OAIQ096A010` of this split); `OAI.CubicFirstMoment.cubicThetaLevelAngularRoot` (definitions bundle `OAIQ096A014` of this split); `OAI.CubicFirstMoment.cubicThetaDualPrefactor` and `OAI.CubicFirstMoment.cubicThetaResidueDualTerm` (definitions bundle `OAIQ096A019` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.Residues`, `OAI.CubicFirstMoment.norm`, `OAI.CubicFirstMoment.primary` and `OAI.CubicFirstMoment.theta` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI.CubicFirstMoment.LogarithmicWeightFamily.cubicTheta_centered_short_low_power`, `OAI.CubicFirstMoment.LogarithmicWeightFamily.cubicTheta_short_low_power`, `OAI.CubicFirstMoment.cubicTheta_completed_negative_tail_mean` and `OAI.CubicFirstMoment.cubicTheta_completed_tail_mean` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaAveragedVoronoi.lean (declaration OAI.CubicFirstMoment.cubicThetaResidue_voronoi)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A019

section

attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators MatrixGroups ContDiff
namespace CubicFirstMoment

theorem cubicThetaResidue_voronoi {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    [Fintype (Residues r)] (rev : Bool) {k : ℕ} (hk : 0<k)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {σ X : ℝ} (hσ : 0<σ) (hX : 0<X) :
    Summable (cubicThetaResidueDualTerm r hr rev k W σ X) ∧
    ((((3^(5/2:ℝ):ℝ):ℂ)*theta (cubicThetaCircleOrder (!rev) k) lambdaE)*
      ((Real.sqrt (norm r):ℂ)*gauss r))*
        metaplecticRawCompleted r (cubicThetaCircleOrder (!rev) k) W X=
    (cubicThetaLevelAngularRoot r rev k)⁻¹*cubicThetaDualPrefactor r*
      ∑' n,cubicThetaResidueDualTerm r hr rev k W σ X n := by
  sorry

end CubicFirstMoment

end

end OAI
end
