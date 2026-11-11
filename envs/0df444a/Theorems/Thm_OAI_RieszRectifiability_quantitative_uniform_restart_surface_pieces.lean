-- Prove2me | Theorems.Thm_OAI_RieszRectifiability_quantitative_uniform_restart_surface_pieces
-- name    : OAI.RieszRectifiability.quantitative_uniform_restart_surface_pieces
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:02.040529+00:00
-- url     : https://prove2.me/theorems/286b2d76-beca-4218-b4d7-a754fdc315ce
-- title:
--   OAI.RieszRectifiability.quantitative_uniform_restart_surface_pieces: intermediate lemma from OpenAI, Riesz transforms and uniform rectifiability in higher codimension
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Riesz transforms and uniform rectifiability in higher codimension*, OpenAI Math Release, September 24, 2026, result family 81, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RieszRectifiability.quantitative_uniform_restart_surface_pieces` of [lean/OAI/Analysis/RieszRectifiability/Uniformity/SurfacePieces.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Uniformity/SurfacePieces.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RieszRectifiability`, with `open MeasureTheory Metric Set Topology`, `open scoped NNReal ENNReal`):
--
--   ```lean
--   theorem quantitative_uniform_restart_surface_pieces {n d : ℕ} (hn : 0 < n) (hnd : n ≤ d)
--       (C G : ℝ) (hC : 1 ≤ C) (hG : 0 < G) :
--       ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 281474976710656 ∧ activeProjectionError d ε ≤ 1 / 128 ∧
--         ∀ δ : ℝ, 0 < δ → ∃ (N : ℕ) (P : ℝ≥0),
--       ∀ (μ : Measure (Ambient d)) [μ.Regular], ADRegularWithConstant n C μ →
--       GlobalUpperGrowth n G μ → ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
--         AdmissibleRadius μ (latticeRadius R k / 8) →
--         let Bad := fun i : SupportCellDescendant μ R hR k z =>
--           ε ≤ bilateralBeta n μ i.center (1024 * i.radius)
--         ∃ (E : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q} → Set (Ambient d))
--           (data : ∀ q : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q},
--             ¬ Bad q.val → SelectedRestartSurfaceData n Bad q.val (E q) ε N P),
--           ∀ q hq, (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G) *
--             (μH[(n : ℝ)] : Measure (Ambient d))
--               ((Set.range (data q hq).model ∩ closedBall q.val.center (3 * q.val.radius)) \ E q) ≤
--                 ENNReal.ofReal δ * μ q.val.cell
--   ```
--
--   **Definitions.** The statement is written with `OAI.RieszRectifiability.GlobalUpperGrowth`, `OAI.RieszRectifiability.SelectedRestartSurfaceData`, `OAI.RieszRectifiability.SupportCellDescendant`, `OAI.RieszRectifiability.activeProjectionError`, `OAI.RieszRectifiability.activeRegionStopMassAreaConstant`, `OAI.RieszRectifiability.bilateralBeta`, `OAI.RieszRectifiability.cellRestartsAfter`, `OAI.RieszRectifiability.latticeRadius`, `OAI.RieszRectifiability.supportCellRoot`, `OAI.RieszRectifiability.supportLatticeNets`, `OAI.RieszRectifiability.SeparatedCover`, `OAI.RieszRectifiability.SupportCellDescendant.cell` and `OAI.RieszRectifiability.SupportCellDescendant.radius` (definitions bundle `OAIQ231Rr000` of this split); `OAI.RieszRectifiability.ADRegularWithConstant`, `OAI.RieszRectifiability.AdmissibleRadius` and `OAI.RieszRectifiability.Ambient` (the published bundle `Def_RieszQuantitative`).
--
--   **Used by.** The proof of `OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability` of this split imports it.
-- source:
--   OpenAI, Riesz transforms and uniform rectifiability in higher codimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 81; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Riesz-transforms-and-uniform-rectifiability-in-higher-codimension-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Uniformity/SurfacePieces.lean (declaration OAI.RieszRectifiability.quantitative_uniform_restart_surface_pieces)

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

theorem quantitative_uniform_restart_surface_pieces {n d : ℕ} (hn : 0 < n) (hnd : n ≤ d)
    (C G : ℝ) (hC : 1 ≤ C) (hG : 0 < G) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 281474976710656 ∧ activeProjectionError d ε ≤ 1 / 128 ∧
      ∀ δ : ℝ, 0 < δ → ∃ (N : ℕ) (P : ℝ≥0),
    ∀ (μ : Measure (Ambient d)) [μ.Regular], ADRegularWithConstant n C μ →
    GlobalUpperGrowth n G μ → ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      let Bad := fun i : SupportCellDescendant μ R hR k z =>
        ε ≤ bilateralBeta n μ i.center (1024 * i.radius)
      ∃ (E : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q} → Set (Ambient d))
        (data : ∀ q : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q},
          ¬ Bad q.val → SelectedRestartSurfaceData n Bad q.val (E q) ε N P),
        ∀ q hq, (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G) *
          (μH[(n : ℝ)] : Measure (Ambient d))
            ((Set.range (data q hq).model ∩ closedBall q.val.center (3 * q.val.radius)) \ E q) ≤
              ENNReal.ofReal δ * μ q.val.cell := by
  sorry

end
end RieszRectifiability

end OAI
end
