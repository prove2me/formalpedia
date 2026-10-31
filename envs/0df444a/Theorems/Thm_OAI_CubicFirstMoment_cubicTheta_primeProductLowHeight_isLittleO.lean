-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_cubicTheta_primeProductLowHeight_isLittleO
-- name    : OAI.CubicFirstMoment.cubicTheta_primeProductLowHeight_isLittleO
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:39:07.074861+00:00
-- url     : https://prove2.me/theorems/3abbae18-d805-4894-bdcb-a7ba1d8289c1
-- title:
--   OAI.CubicFirstMoment.cubicTheta_primeProductLowHeight_isLittleO: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.cubicTheta_primeProductLowHeight_isLittleO` of [lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaPrimeComparison.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaPrimeComparison.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Filter Asymptotics`):
--
--   ```lean
--   lemma cubicTheta_primeProductLowHeight_isLittleO (ℓ : ℤ) (Ct : ℕ)
--       (H : ℝ → ℝ) (hH : ∀ᶠ X : ℝ in atTop,0<H X) :
--       (fun X => primeProductLowHeight ℓ (H X) ((1+Real.log X)^Ct) X)
--         =o[atTop] firstMomentScale
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.primeProductLowHeight` (definitions bundle `OAIQ096A019` of this split); `OAI.CubicFirstMoment.firstMomentScale` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.patterson_angularComparison` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaPrimeComparison.lean (declaration OAI.CubicFirstMoment.cubicTheta_primeProductLowHeight_isLittleO)

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A019

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Asymptotics
namespace CubicFirstMoment

lemma cubicTheta_primeProductLowHeight_isLittleO (ℓ : ℤ) (Ct : ℕ)
    (H : ℝ → ℝ) (hH : ∀ᶠ X : ℝ in atTop,0<H X) :
    (fun X => primeProductLowHeight ℓ (H X) ((1+Real.log X)^Ct) X)
      =o[atTop] firstMomentScale := by
  sorry

end CubicFirstMoment

end

end OAI
end
