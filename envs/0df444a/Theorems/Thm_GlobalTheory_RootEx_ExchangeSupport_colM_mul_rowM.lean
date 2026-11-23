-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_colM_mul_rowM
-- name    : GlobalTheory.RootEx.ExchangeSupport.colM_mul_rowM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:54:49.298848+00:00
-- url     : https://prove2.me/theorems/7de23430-e528-4c0f-bcf9-41ef897afc09
-- title:
--   Exchange Support: col M mul row M
-- statement:
--   The Exchange Support construction uses the col M mul row M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeSupportAndFourierRelation.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeSupportAndFourierRelation.lean#L24-L30

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
omit [DecidableEq n] [Fintype n]

theorem GlobalTheory.RootEx.ExchangeSupport.colM_mul_rowM (u β : n → k) : colM c (p + 1) β * rowM c p u = 0 := by sorry
