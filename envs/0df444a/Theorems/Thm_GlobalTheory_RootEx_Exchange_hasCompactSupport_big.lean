-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Exchange_hasCompactSupport_big
-- name    : GlobalTheory.RootEx.Exchange.hasCompactSupport_big
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:23:52.951042+00:00
-- url     : https://prove2.me/theorems/d10519a6-eade-4b46-82eb-b7d2a31a719f
-- title:
--   Exchange: has Compact Support big
-- statement:
--   The Exchange construction uses the has Compact Support big property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContinuousWittExtendByZero.lean#L265-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContinuousWittExtendByZero.lean#L265-L279

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Exchange
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem GlobalTheory.RootEx.Exchange.hasCompactSupport_big (ψ : AddChar k Circle) (q : Fin c) (χ : (n' → k) → ℂ)
    {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} (hΦ : HasCompactSupport Φ) (x₀ : Matrix n n' k) :
    HasCompactSupport fun y => big ψ q χ Φ (mat x₀ y) := by sorry
