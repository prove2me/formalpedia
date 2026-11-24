-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_om_smul_add
-- name    : GlobalTheory.SplitWeil.om_smul_add
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:21:07.842019+00:00
-- url     : https://prove2.me/theorems/1ded2247-c387-4785-b5b6-41bd7c3bba65
-- title:
--   Split Weil: om smul add
-- statement:
--   The Split Weil construction uses the om smul add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyCompSideMulEq.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyCompSideMulEq.lean#L14-L18

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

theorem GlobalTheory.SplitWeil.om_smul_add (μ : kˣ →* ℂˣ) (g : GL a k) (h : GL b k) (z : ℂ) (Φ Ψ : Matrix b a k → ℂ) :
    om μ g h (z • Φ + Ψ) = z • om μ g h Φ + om μ g h Ψ := by sorry
