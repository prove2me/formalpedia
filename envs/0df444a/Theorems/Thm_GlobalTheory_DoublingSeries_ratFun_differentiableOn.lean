-- Prove2me | Theorems.Thm_GlobalTheory_DoublingSeries_ratFun_differentiableOn
-- name    : GlobalTheory.DoublingSeries.ratFun_differentiableOn
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:13:24.388123+00:00
-- url     : https://prove2.me/theorems/a6095846-55ee-4c1d-9679-c3da8fa510ee
-- title:
--   Doubling Series: rat Fun differentiable On
-- statement:
--   The Doubling Series construction uses the rat Fun differentiable On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RatFunDifferentiableOn.lean#L24-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RatFunDifferentiableOn.lean#L24-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BorelParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RatFunDifferentiableOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
noncomputable section
open GlobalTheory GlobalTheory.DoublingSeries

theorem GlobalTheory.DoublingSeries.ratFun_differentiableOn {q : ℕ} (hq : 1 < q) (N : ℕ) (α : Fin N → ℂˣ) (ρ : ℝ)
    (hα : ∀ x, ‖(α x : ℂ)‖ ≤ (q : ℝ) ^ ρ ∧ ‖(α x : ℂ)‖⁻¹ ≤ (q : ℝ) ^ ρ) :
    DifferentiableOn ℂ (ratFun q N α) (Metric.ball 0 ((q : ℝ) ^ (1 / 2 - ρ))) := by sorry
