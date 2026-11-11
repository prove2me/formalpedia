-- Prove2me | Theorems.Thm_OAI_RieszRectifiability_active_region_limit_area_le_original_top
-- name    : OAI.RieszRectifiability.active_region_limit_area_le_original_top
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:22:59.59771+00:00
-- url     : https://prove2.me/theorems/96e38fcf-c0d8-4458-9116-b768797a7364
-- title:
--   OAI.RieszRectifiability.active_region_limit_area_le_original_top: intermediate lemma from OpenAI, Riesz transforms and uniform rectifiability in higher codimension
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Riesz transforms and uniform rectifiability in higher codimension*, OpenAI Math Release, September 24, 2026, result family 81, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RieszRectifiability.active_region_limit_area_le_original_top` of [lean/OAI/Analysis/RieszRectifiability/Restart/ActiveRegionUniformArea.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Restart/ActiveRegionUniformArea.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RieszRectifiability`, with `open MeasureTheory Metric Set`, `open scoped NNReal ENNReal`):
--
--   ```lean
--   theorem active_region_limit_area_le_original_top {n d : ℕ}
--       (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
--       (hg : GlobalUpperGrowth n G μ)
--       (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
--         ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
--       (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
--       (z : (supportLatticeNets μ R hR k).points)
--       (Good : SupportCellDescendant μ R hR k z → Prop)
--       (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
--       (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
--       (hεfine : ε ≤ 1 / 281474976710656) (hsmall : activeProjectionError d ε ≤ 1 / 128)
--       (hfit : ∀ i, activeRegionCell Good i →
--         bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
--       (f : S (supportCellRoot μ R hR k z) → Ambient d)
--       (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f) :
--       (μH[(n : ℝ)] : Measure (Ambient d))
--         (Set.range f ∩ closedBall (z : Ambient d) (2 * latticeRadius R k)) ≤
--         activeRegionUniformAreaConstant n d C G * μ (cleanSupportCell μ R hR k z)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RieszRectifiability.GlobalUpperGrowth`, `OAI.RieszRectifiability.IsActiveRegionLimitModel`, `OAI.RieszRectifiability.IsAffineNPlane`, `OAI.RieszRectifiability.SupportCellDescendant`, `OAI.RieszRectifiability.activeProjectionError`, `OAI.RieszRectifiability.activeRegionCell`, `OAI.RieszRectifiability.activeRegionUniformAreaConstant`, `OAI.RieszRectifiability.bilateralPlaneError`, `OAI.RieszRectifiability.cleanSupportCell`, `OAI.RieszRectifiability.latticeRadius`, `OAI.RieszRectifiability.supportCellRoot`, `OAI.RieszRectifiability.supportLatticeNets`, `OAI.RieszRectifiability.SeparatedCover` and `OAI.RieszRectifiability.SupportCellDescendant.radius` (definitions bundle `OAIQ231Rr000` of this split); `OAI.RieszRectifiability.AdmissibleRadius` and `OAI.RieszRectifiability.Ambient` (the published bundle `Def_RieszQuantitative`).
--
--   **Used by.** The proof of `OAI.RieszRectifiability.quantitative_uniform_precision_area_models` of this split imports it.
-- source:
--   OpenAI, Riesz transforms and uniform rectifiability in higher codimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 81; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Riesz-transforms-and-uniform-rectifiability-in-higher-codimension-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Restart/ActiveRegionUniformArea.lean (declaration OAI.RieszRectifiability.active_region_limit_area_le_original_top)

import Mathlib
import Definitions.Def_RieszQuantitative
import Definitions.Def_OAIQ231Rr000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem active_region_limit_area_le_original_top {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεfine : ε ≤ 1 / 281474976710656) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f) :
    (μH[(n : ℝ)] : Measure (Ambient d))
      (Set.range f ∩ closedBall (z : Ambient d) (2 * latticeRadius R k)) ≤
      activeRegionUniformAreaConstant n d C G * μ (cleanSupportCell μ R hR k z) := by
  sorry

end

end RieszRectifiability

end OAI
end
