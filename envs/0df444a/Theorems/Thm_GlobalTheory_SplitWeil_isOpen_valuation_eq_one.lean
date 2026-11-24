-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_isOpen_valuation_eq_one
-- name    : GlobalTheory.SplitWeil.isOpen_valuation_eq_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:21:04.799242+00:00
-- url     : https://prove2.me/theorems/b1d099ec-285b-4eb7-a6f5-0fe126f073d3
-- title:
--   Split Weil: is Open valuation eq one
-- statement:
--   The Split Weil construction uses the is Open valuation eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyCompSideMulEq.lean#L56-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyCompSideMulEq.lean#L56-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
open GlobalTheory GlobalTheory.SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem GlobalTheory.SplitWeil.isOpen_valuation_eq_one : IsOpen {x : kˣ | valuation k (x : k) = 1} := by sorry
