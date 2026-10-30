-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_cubicThetaScalarRankinKernel_integral_limit
-- name    : OAI.CubicFirstMoment.cubicThetaScalarRankinKernel_integral_limit
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T04:39:21.549525+00:00
-- url     : https://prove2.me/theorems/504cb861-934c-4549-b61d-e52ff03d1fa5
-- title:
--   OAI.CubicFirstMoment.cubicThetaScalarRankinKernel_integral_limit: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.cubicThetaScalarRankinKernel_integral_limit` of [lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaRankinConvergence.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaRankinConvergence.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open MeasureTheory Filter Set`, `open scoped Topology`):
--
--   ```lean
--   theorem cubicThetaScalarRankinKernel_integral_limit
--       (F : CubicThetaQuotient → ℂ) (hF : Integrable F cubicThetaQuotientMeasure) :
--       Tendsto (fun σ : ℝ => ∫ q,(σ:ℂ)*(cubicThetaScalarRankinKernel σ q:ℂ)*F q
--           ∂cubicThetaQuotientMeasure) (𝓝[>] 0)
--         (𝓝 (((Real.pi:ℂ)^2/(108*principalIdealZeta 2))*
--           ∫ q,F q ∂cubicThetaQuotientMeasure))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.CubicThetaQuotient`, `OAI.CubicFirstMoment.cubicThetaQuotientMeasure` and `OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.cubicThetaScalarRankinKernel` (definitions bundle `OAIQ096A014` of this split); `OAI.CubicFirstMoment.principalIdealZeta` (definitions bundle `OAIQ096A016` of this split).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.cubicThetaActualCompletedRadialMain_eq` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaRankinConvergence.lean (declaration OAI.CubicFirstMoment.cubicThetaScalarRankinKernel_integral_limit)

import Mathlib
import Definitions.Def_OAIQ096A014
import Definitions.Def_OAIQ096A016

section

attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace CubicFirstMoment

theorem cubicThetaScalarRankinKernel_integral_limit
    (F : CubicThetaQuotient → ℂ) (hF : Integrable F cubicThetaQuotientMeasure) :
    Tendsto (fun σ : ℝ => ∫ q,(σ:ℂ)*(cubicThetaScalarRankinKernel σ q:ℂ)*F q
        ∂cubicThetaQuotientMeasure) (𝓝[>] 0)
      (𝓝 (((Real.pi:ℂ)^2/(108*principalIdealZeta 2))*
        ∫ q,F q ∂cubicThetaQuotientMeasure)) := by
  sorry

end CubicFirstMoment

end

end OAI
end
