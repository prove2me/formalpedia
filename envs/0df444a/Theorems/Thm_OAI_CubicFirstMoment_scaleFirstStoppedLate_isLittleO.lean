-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_scaleFirstStoppedLate_isLittleO
-- name    : OAI.CubicFirstMoment.scaleFirstStoppedLate_isLittleO
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T04:44:14.881213+00:00
-- url     : https://prove2.me/theorems/b4790055-c2cf-45ac-b092-f68676d15560
-- title:
--   OAI.CubicFirstMoment.scaleFirstStoppedLate_isLittleO: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.scaleFirstStoppedLate_isLittleO` of [lean/OAI/NumberTheory/CubicMoment/Estimates/ScaleFirstLateNegligible.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/ScaleFirstLateNegligible.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Filter`, `open scoped BigOperators`):
--
--   ```lean
--   theorem scaleFirstStoppedLate_isLittleO (m : ℕ) (hpnt : PrimaryPrimePNT)
--       {C ξ ρ ε : ℝ} (hC : 0 < C) (hξ : 0 < ξ)
--       (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε)
--       (hgap : ξ+ε < 1/100) (Ct : ℕ) (H : ℝ → ℝ) (h : ℝ → ℕ)
--       (hH : ∀ᶠ X : ℝ in atTop, 0 < H X)
--       (hh : ∀ᶠ X : ℝ in atTop,
--         geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X ≤ h X)
--       (hboundary : ∀ᶠ X : ℝ in atTop,
--         ρ*geometricBinLower ρ (Real.exp primeProductWeights.radius*X) (h X) ≤ (Real.log X)^C) :
--       (fun X => scaleFirstStoppedSum m ρ ξ Ct (H X) X (h X) false)
--         =o[atTop] firstMomentScale
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.UniformLogWeights` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.geometricBinCount`, `OAI.CubicFirstMoment.geometricBinLower` and `OAI.CubicFirstMoment.primeProductEnvelope` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.primeProductWeights` (definitions bundle `OAIQ096A005` of this split); `OAI.CubicFirstMoment.PrimaryPrimePNT` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.scaleFirstStoppedSum` (definitions bundle `OAIQ096A019` of this split); `OAI.CubicFirstMoment.firstMomentScale` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.primeProductLowHeight_radial_isLittleO_actual` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/ScaleFirstLateNegligible.lean (declaration OAI.CubicFirstMoment.scaleFirstStoppedLate_isLittleO)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A019

section

attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem scaleFirstStoppedLate_isLittleO (m : ℕ) (hpnt : PrimaryPrimePNT)
    {C ξ ρ ε : ℝ} (hC : 0 < C) (hξ : 0 < ξ)
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε)
    (hgap : ξ+ε < 1/100) (Ct : ℕ) (H : ℝ → ℝ) (h : ℝ → ℕ)
    (hH : ∀ᶠ X : ℝ in atTop, 0 < H X)
    (hh : ∀ᶠ X : ℝ in atTop,
      geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X ≤ h X)
    (hboundary : ∀ᶠ X : ℝ in atTop,
      ρ*geometricBinLower ρ (Real.exp primeProductWeights.radius*X) (h X) ≤ (Real.log X)^C) :
    (fun X => scaleFirstStoppedSum m ρ ξ Ct (H X) X (h X) false)
      =o[atTop] firstMomentScale := by
  sorry

end CubicFirstMoment

end

end OAI
end
