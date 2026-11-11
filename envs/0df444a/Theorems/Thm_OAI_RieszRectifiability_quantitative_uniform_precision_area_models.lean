-- Prove2me | Theorems.Thm_OAI_RieszRectifiability_quantitative_uniform_precision_area_models
-- name    : OAI.RieszRectifiability.quantitative_uniform_precision_area_models
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:25:54.889471+00:00
-- url     : https://prove2.me/theorems/ab2142a2-33f0-4c26-b4ae-5938207b3bf6
-- title:
--   OAI.RieszRectifiability.quantitative_uniform_precision_area_models: intermediate lemma from OpenAI, Riesz transforms and uniform rectifiability in higher codimension
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Riesz transforms and uniform rectifiability in higher codimension*, OpenAI Math Release, September 24, 2026, result family 81, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RieszRectifiability.quantitative_uniform_precision_area_models` of [lean/OAI/Analysis/RieszRectifiability/Uniformity/SurfacePieces.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Uniformity/SurfacePieces.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RieszRectifiability`, with `open MeasureTheory Metric Set Topology`, `open scoped NNReal ENNReal`):
--
--   ```lean
--   theorem quantitative_uniform_precision_area_models {n d : ℕ} (hn : 0 < n) (hnd : n ≤ d)
--       (C G : ℝ) (hC : 1 ≤ C) (hG : 0 < G) :
--       ∃ Ktop : ℝ≥0∞, Ktop < ⊤ ∧ ∃ Kupper : ℝ≥0∞, Kupper < ⊤ ∧
--         ∃ Klower : ℝ≥0∞, 0 < Klower ∧ Klower < ⊤ ∧
--         ∀ (μ : Measure (Ambient d)) [μ.Regular], ADRegularWithConstant n C μ →
--         GlobalUpperGrowth n G μ → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 281474976710656 → activeProjectionError d ε ≤ 1 / 128 →
--         ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
--           AdmissibleRadius μ (latticeRadius R k / 8) →
--           let Good := fun q : SupportCellDescendant μ R hR k z =>
--             bilateralBeta n μ q.center (1024 * q.radius) < ε
--           ∃ (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
--             (hS : ∀ i, IsAffineNPlane n (S i)),
--             (∀ i, activeRegionCell Good i → bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε) ∧
--             ∃ f : S (supportCellRoot μ R hR k z) → Ambient d,
--               IsActiveRegionLimitModel μ R hR k z Good S hS ε f ∧ IsClosedEmbedding f ∧
--               (μH[(n : ℝ)] : Measure (Ambient d))
--                 (Set.range f ∩ closedBall (z : Ambient d) (2 * latticeRadius R k)) ≤
--                   Ktop * μ (cleanSupportCell μ R hR k z) ∧
--               (∀ (p : Ambient d) (r : ℝ), 0 < r →
--                 (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall p r) ≤
--                   Kupper * (ENNReal.ofReal r) ^ n) ∧
--               ∀ p ∈ Set.range f, ∀ (r : ℝ), 0 < r →
--                 Klower * (ENNReal.ofReal r) ^ n ≤
--                   (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall p r)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RieszRectifiability.GlobalUpperGrowth`, `OAI.RieszRectifiability.IsActiveRegionLimitModel`, `OAI.RieszRectifiability.IsAffineNPlane`, `OAI.RieszRectifiability.SupportCellDescendant`, `OAI.RieszRectifiability.activeProjectionError`, `OAI.RieszRectifiability.activeRegionCell`, `OAI.RieszRectifiability.bilateralBeta`, `OAI.RieszRectifiability.bilateralPlaneError`, `OAI.RieszRectifiability.cleanSupportCell`, `OAI.RieszRectifiability.latticeRadius`, `OAI.RieszRectifiability.supportCellRoot`, `OAI.RieszRectifiability.supportLatticeNets`, `OAI.RieszRectifiability.SeparatedCover` and `OAI.RieszRectifiability.SupportCellDescendant.radius` (definitions bundle `OAIQ231Rr000` of this split); `OAI.RieszRectifiability.ADRegularWithConstant`, `OAI.RieszRectifiability.AdmissibleRadius` and `OAI.RieszRectifiability.Ambient` (the published bundle `Def_RieszQuantitative`).
--
--   **Used by.** The proof of `OAI.RieszRectifiability.quantitative_uniform_restart_surface_pieces` of this split imports it.
-- source:
--   OpenAI, Riesz transforms and uniform rectifiability in higher codimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 81; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Riesz-transforms-and-uniform-rectifiability-in-higher-codimension-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Uniformity/SurfacePieces.lean (declaration OAI.RieszRectifiability.quantitative_uniform_precision_area_models)

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Tactic
import Mathlib.Topology.Defs.Basic
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
open MeasureTheory Metric Set Topology
open scoped NNReal ENNReal

theorem quantitative_uniform_precision_area_models {n d : ℕ} (hn : 0 < n) (hnd : n ≤ d)
    (C G : ℝ) (hC : 1 ≤ C) (hG : 0 < G) :
    ∃ Ktop : ℝ≥0∞, Ktop < ⊤ ∧ ∃ Kupper : ℝ≥0∞, Kupper < ⊤ ∧
      ∃ Klower : ℝ≥0∞, 0 < Klower ∧ Klower < ⊤ ∧
      ∀ (μ : Measure (Ambient d)) [μ.Regular], ADRegularWithConstant n C μ →
      GlobalUpperGrowth n G μ → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 281474976710656 → activeProjectionError d ε ≤ 1 / 128 →
      ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
        AdmissibleRadius μ (latticeRadius R k / 8) →
        let Good := fun q : SupportCellDescendant μ R hR k z =>
          bilateralBeta n μ q.center (1024 * q.radius) < ε
        ∃ (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
          (hS : ∀ i, IsAffineNPlane n (S i)),
          (∀ i, activeRegionCell Good i → bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε) ∧
          ∃ f : S (supportCellRoot μ R hR k z) → Ambient d,
            IsActiveRegionLimitModel μ R hR k z Good S hS ε f ∧ IsClosedEmbedding f ∧
            (μH[(n : ℝ)] : Measure (Ambient d))
              (Set.range f ∩ closedBall (z : Ambient d) (2 * latticeRadius R k)) ≤
                Ktop * μ (cleanSupportCell μ R hR k z) ∧
            (∀ (p : Ambient d) (r : ℝ), 0 < r →
              (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall p r) ≤
                Kupper * (ENNReal.ofReal r) ^ n) ∧
            ∀ p ∈ Set.range f, ∀ (r : ℝ), 0 < r →
              Klower * (ENNReal.ofReal r) ^ n ≤
                (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall p r) := by
  sorry

end
end RieszRectifiability

end OAI
end
