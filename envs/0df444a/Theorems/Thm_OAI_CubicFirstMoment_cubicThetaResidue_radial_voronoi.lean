-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_cubicThetaResidue_radial_voronoi
-- name    : OAI.CubicFirstMoment.cubicThetaResidue_radial_voronoi
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:37:47.26927+00:00
-- url     : https://prove2.me/theorems/37ae5852-0b0c-4905-ae3b-9dd0e235ef06
-- title:
--   OAI.CubicFirstMoment.cubicThetaResidue_radial_voronoi: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.cubicThetaResidue_radial_voronoi` of [lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaRadialAverage.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaRadialAverage.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open scoped BigOperators MatrixGroups ContDiff`):
--
--   ```lean
--   theorem cubicThetaResidue_radial_voronoi {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
--       [Fintype (Residues r)] (W : ℝ→ℂ) (hW : HasCompactSupport W)
--       (hpos : tsupport W⊆Set.Ioi 0) (hsm : ContDiff ℝ ∞ W)
--       {σ X : ℝ} (hσ : 0<σ) (hX : 0<X) :
--       Summable (cubicThetaResidueDualTerm r hr false 0 W σ X) ∧
--       (((3^(5/2:ℝ):ℝ):ℂ)*((Real.sqrt (norm r):ℂ)*gauss r))*
--         metaplecticRawCompleted r 0 W X=
--         cubicThetaDualPrefactor r*∑' n,cubicThetaResidueDualTerm r hr false 0 W σ X n+
--           cubicThetaResidueRadialPole r*mellin W (5/6)*((X/27:ℝ):ℂ)^(5/6:ℂ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.MetaplecticDualArgument` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.gauss` (definitions bundle `OAIQ096A005` of this split); `OAI.CubicFirstMoment.metaplecticRawCompleted` (definitions bundle `OAIQ096A010` of this split); `OAI.CubicFirstMoment.cubicThetaResidueRadialPole` (definitions bundle `OAIQ096A016` of this split); `OAI.CubicFirstMoment.cubicThetaDualPrefactor` and `OAI.CubicFirstMoment.cubicThetaResidueDualTerm` (definitions bundle `OAIQ096A019` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.Residues`, `OAI.CubicFirstMoment.norm` and `OAI.CubicFirstMoment.primary` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI.CubicFirstMoment.LogarithmicWeightFamily.cubicTheta_centered_short_low_power`, `OAI.CubicFirstMoment.cubicTheta_radial_remainder_negative_tail_mean` and `OAI.CubicFirstMoment.cubicTheta_radial_remainder_tail_mean` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaRadialAverage.lean (declaration OAI.CubicFirstMoment.cubicThetaResidue_radial_voronoi)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A016
import Definitions.Def_OAIQ096A019

section

attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators MatrixGroups ContDiff
namespace CubicFirstMoment

theorem cubicThetaResidue_radial_voronoi {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    [Fintype (Residues r)] (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W⊆Set.Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {σ X : ℝ} (hσ : 0<σ) (hX : 0<X) :
    Summable (cubicThetaResidueDualTerm r hr false 0 W σ X) ∧
    (((3^(5/2:ℝ):ℝ):ℂ)*((Real.sqrt (norm r):ℂ)*gauss r))*
      metaplecticRawCompleted r 0 W X=
      cubicThetaDualPrefactor r*∑' n,cubicThetaResidueDualTerm r hr false 0 W σ X n+
        cubicThetaResidueRadialPole r*mellin W (5/6)*((X/27:ℝ):ℂ)^(5/6:ℂ) := by
  sorry

end CubicFirstMoment

end

end OAI
end
