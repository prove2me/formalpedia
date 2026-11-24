-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_conj_row
-- name    : GlobalTheory.RootEx.ExchangeSupport.conj_row
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:24:25.129362+00:00
-- url     : https://prove2.me/theorems/ac732bb7-5be1-415c-bc9f-e4c667c9d492
-- title:
--   Exchange Support: conj row
-- statement:
--   The Exchange Support construction uses the conj row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeSupportAndFourierRelation.lean#L106-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeSupportAndFourierRelation.lean#L106-L125

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

theorem GlobalTheory.RootEx.ExchangeSupport.conj_row (hp : 1 ≤ p) (hc : p < c) (u β : n → k) :
    colE c (p + 1) β * rowE c p u * (colE c (p + 1) β)⁻¹ ∈ N k n c (p + 1) ∧
      simpleSum (colE c (p + 1) β * rowE c p u * (colE c (p + 1) β)⁻¹) = -(u ⬝ᵥ β) := by sorry
