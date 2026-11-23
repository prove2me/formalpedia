-- Prove2me | Theorems.Thm_GlobalTheory_RootExchangeFixed_ball_eq
-- name    : GlobalTheory.RootExchangeFixed.ball_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:44.704935+00:00
-- url     : https://prove2.me/theorems/e99466db-b6f2-4a7a-a846-a47415f6083b
-- title:
--   Root Exchange Fixed: ball eq
-- statement:
--   The Root Exchange Fixed construction uses the ball eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NonarchimedeanLocalFieldSecondCountableT2Space.lean#L156-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NonarchimedeanLocalFieldSecondCountableT2Space.lean#L156-L162

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NonarchimedeanLocalFieldSecondCountableT2Space
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Pointwise
open GlobalTheory GlobalTheory.RootExchangeFixed
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.RootExchangeFixed.ball_eq (s : kˣ) : {x : k | valuation k x ≤ valuation k (s : k)} = s • (𝒪[k] : Set k) := by sorry
