-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_cubicThetaArithmeticRankinMass_unfold
-- name    : OAI.CubicFirstMoment.cubicThetaArithmeticRankinMass_unfold
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T04:53:00.326979+00:00
-- url     : https://prove2.me/theorems/0d6a421a-4827-4bcf-a71b-03705cdf02e4
-- title:
--   OAI.CubicFirstMoment.cubicThetaArithmeticRankinMass_unfold: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.cubicThetaArithmeticRankinMass_unfold` of [lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaRankinUnfold.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaRankinUnfold.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open MeasureTheory Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem cubicThetaArithmeticRankinMass_unfold :
--       ∀ᶠ σ : ℝ in 𝓝[>] 0,
--         Integrable (cubicThetaScalarEnergySeed cubicThetaArithmeticModelSection σ)
--           cubicThetaPointMeasure ∧
--         cubicThetaArithmeticRankinMass σ=
--           ∫ p,(cubicThetaScalarEnergySeed cubicThetaArithmeticModelSection σ p:ℂ)
--             ∂cubicThetaPointMeasure
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.CubicThetaPoint`, `OAI.CubicFirstMoment.cubicThetaPointMeasure` and `OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.cubicThetaScalarEnergySeed` (definitions bundle `OAIQ096A019` of this split); `OAI.CubicFirstMoment.cubicThetaArithmeticModelSection` and `OAI.CubicFirstMoment.cubicThetaArithmeticRankinMass` (definitions bundle `OAIQ096A026` of this split).
--
--   **Used by.** The proofs of `OAI.CubicFirstMoment.cubicThetaActualCompletedRadialMain_eq` and `OAI_CubicFirstMoment_cubicThetaArithmeticBaseScalar_sign` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaRankinUnfold.lean (declaration OAI.CubicFirstMoment.cubicThetaArithmeticRankinMass_unfold)

import Mathlib
import Definitions.Def_OAIQ096A026

section

attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace CubicFirstMoment

theorem cubicThetaArithmeticRankinMass_unfold :
    ∀ᶠ σ : ℝ in 𝓝[>] 0,
      Integrable (cubicThetaScalarEnergySeed cubicThetaArithmeticModelSection σ)
        cubicThetaPointMeasure ∧
      cubicThetaArithmeticRankinMass σ=
        ∫ p,(cubicThetaScalarEnergySeed cubicThetaArithmeticModelSection σ p:ℂ)
          ∂cubicThetaPointMeasure := by
  sorry

end CubicFirstMoment

end

end OAI
end
