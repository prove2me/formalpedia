-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_colE_inv_val
-- name    : GlobalTheory.RootEx.ExchangeSupport.colE_inv_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:54:36.476481+00:00
-- url     : https://prove2.me/theorems/b0ef998d-c0fd-44d1-8f25-99b839d406e9
-- title:
--   Exchange Support: col E inv val
-- statement:
--   The Exchange Support construction uses the col E inv val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeSupportAndFourierRelation.lean#L21-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeSupportAndFourierRelation.lean#L21-L21

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

theorem GlobalTheory.RootEx.ExchangeSupport.colE_inv_val (u : n → k) : ((colE c p u)⁻¹).val = fromBlocks 1 (-colM c p u) 0 1 := by sorry
