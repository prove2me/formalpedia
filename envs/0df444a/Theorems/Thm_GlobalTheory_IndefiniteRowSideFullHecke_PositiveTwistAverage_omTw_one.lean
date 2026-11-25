-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PositiveTwistAverage_omTw_one
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage.omTw_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:09:36.048949+00:00
-- url     : https://prove2.me/theorems/1a746561-e6f5-50ee-8291-0ef03cc8e73d
-- title:
--   Positive Twist Average: om Tw one
-- statement:
--   The Positive Twist Average construction uses the om Tw one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/PositiveTwistAverage.lean#L114-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/PositiveTwistAverage.lean#L114-L116

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PositiveTwistAverage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable {P P' A A' : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup P'] [Module ℂ P']
  [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A']
variable [MeasurableSpace k] [BorelSpace k]
omit [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage.omTw_one {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ) : omTw μ 1 1 g h Φ = om μ g h Φ := by sorry
