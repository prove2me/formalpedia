-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_rowM_mul_colM
-- name    : GlobalTheory.RootEx.ExchangeSupport.rowM_mul_colM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:54:24.362822+00:00
-- url     : https://prove2.me/theorems/99073255-8633-42ae-830f-62014d6aa738
-- title:
--   Exchange Support: row M mul col M
-- statement:
--   The Exchange Support construction uses the row M mul col M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeSupportAndFourierRelation.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeSupportAndFourierRelation.lean#L33-L36

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
omit [DecidableEq n]

theorem GlobalTheory.RootEx.ExchangeSupport.rowM_mul_colM (u β : n → k) (i j : Fin c) :
    (rowM c p u * colM c (p + 1) β) i j = if i.val + 1 = p ∧ j.val = p then u ⬝ᵥ β else 0 := by sorry
