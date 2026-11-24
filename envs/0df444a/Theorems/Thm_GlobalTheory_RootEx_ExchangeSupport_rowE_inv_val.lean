-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_rowE_inv_val
-- name    : GlobalTheory.RootEx.ExchangeSupport.rowE_inv_val
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:26:04.316024+00:00
-- url     : https://prove2.me/theorems/2dcd333e-7300-40ae-8bdd-1ee0d54c29ce
-- title:
--   Exchange Support: row E inv val
-- statement:
--   The Exchange Support construction uses the row E inv val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeSupportAndFourierRelation.lean#L20-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeSupportAndFourierRelation.lean#L20-L20

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

theorem GlobalTheory.RootEx.ExchangeSupport.rowE_inv_val (u : n → k) : ((rowE c p u)⁻¹).val = fromBlocks 1 0 (-rowM c p u) 1 := by sorry
