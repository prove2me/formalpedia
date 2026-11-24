-- Prove2me | Theorems.Thm_GlobalTheory_DoublingSeries_cpow_split
-- name    : GlobalTheory.DoublingSeries.cpow_split
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:14:39.791157+00:00
-- url     : https://prove2.me/theorems/d2e11cae-3c87-43c6-93ca-254f057b54e0
-- title:
--   Doubling Series: cpow split
-- statement:
--   The Doubling Series construction uses the cpow split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RatFunDifferentiableOn.lean#L72-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RatFunDifferentiableOn.lean#L72-L81

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

theorem GlobalTheory.DoublingSeries.cpow_split {q : ℕ} (hq : 1 < q) (N : ℕ) (s : ℂ) {m : ℤ} (hm : 0 ≤ m) :
    (q : ℂ) ^ (-((N : ℂ) / 2 + s) * (m : ℂ)) =
      (((q : ℝ) ^ (-((N : ℝ) / 2) * (m : ℝ)) : ℝ) : ℂ) * ((q : ℂ) ^ (-s)) ^ m.toNat := by sorry
