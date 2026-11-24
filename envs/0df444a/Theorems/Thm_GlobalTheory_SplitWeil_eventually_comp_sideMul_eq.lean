-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_eventually_comp_sideMul_eq
-- name    : GlobalTheory.SplitWeil.eventually_comp_sideMul_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:21:50.741746+00:00
-- url     : https://prove2.me/theorems/5b4d92ba-2886-45ea-969a-bc2a028d5e8d
-- title:
--   Split Weil: eventually comp side Mul eq
-- statement:
--   The Split Weil construction uses the eventually comp side Mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyCompSideMulEq.lean#L20-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyCompSideMulEq.lean#L20-L54

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

theorem GlobalTheory.SplitWeil.eventually_comp_sideMul_eq {Φ : Matrix b a k → ℂ} (hΦ : Φ ∈ SB (Matrix b a k)) :
    ∀ᶠ gh : GL a k × GL b k in 𝓝 1, ∀ x, Φ (sideMul gh.1 gh.2 x) = Φ x := by sorry
