-- Prove2me | Theorems.Thm_GlobalTheory_DoublingSeries_exists_cpow_neg_eq
-- name    : GlobalTheory.DoublingSeries.exists_cpow_neg_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:14:13.593083+00:00
-- url     : https://prove2.me/theorems/9522f475-5b22-4ed3-9db8-a002bf2b3465
-- title:
--   Doubling Series: exists cpow neg eq
-- statement:
--   The Doubling Series construction uses the exists cpow neg eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RatFunDifferentiableOn.lean#L55-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RatFunDifferentiableOn.lean#L55-L70

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

theorem GlobalTheory.DoublingSeries.exists_cpow_neg_eq {q : ℕ} (hq : 1 < q) (s₀ : ℝ) {z : ℂ} (hz : z ≠ 0) (hzs : ‖z‖ < (q : ℝ) ^ (-s₀)) :
    ∃ s : ℂ, s₀ < s.re ∧ (q : ℂ) ^ (-s) = z := by sorry
