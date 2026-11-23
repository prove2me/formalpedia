-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_rowE_val
-- name    : GlobalTheory.RootEx.ExchangeSupport.rowE_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:50:31.730068+00:00
-- url     : https://prove2.me/theorems/2996d16f-4029-4d47-8820-749b131aadc9
-- title:
--   Exchange Support: row E val
-- statement:
--   The Exchange Support construction uses the row E val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeSupportAndFourierRelation.lean#L18-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeSupportAndFourierRelation.lean#L18-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.ExchangeSupport
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem GlobalTheory.RootEx.ExchangeSupport.rowE_val (u : n → k) : (rowE c p u).val = fromBlocks 1 0 (rowM c p u) 1 := by sorry
