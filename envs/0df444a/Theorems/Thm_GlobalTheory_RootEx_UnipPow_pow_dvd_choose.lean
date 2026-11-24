-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_UnipPow_pow_dvd_choose
-- name    : GlobalTheory.RootEx.UnipPow.pow_dvd_choose
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:09:32.744151+00:00
-- url     : https://prove2.me/theorems/4abdcb9c-efaf-4c84-8584-407baed13a77
-- title:
--   Unip Pow: pow dvd choose
-- statement:
--   The Unip Pow construction uses the pow dvd choose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentExistsResidueCardPowMemNhds.lean#L8-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentExistsResidueCardPowMemNhds.lean#L8-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentExistsResidueCardPowMemNhds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnipPow

theorem GlobalTheory.RootEx.UnipPow.pow_dvd_choose {q : ℕ} (hq : q.Prime) (m : ℕ) {i : ℕ} (hi : i ≠ 0) :
    q ^ (m - i) ∣ (q ^ m).choose i := by sorry
