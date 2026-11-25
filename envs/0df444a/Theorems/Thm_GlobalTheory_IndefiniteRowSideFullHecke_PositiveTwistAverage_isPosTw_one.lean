-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PositiveTwistAverage_isPosTw_one
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage.isPosTw_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:09:39.384249+00:00
-- url     : https://prove2.me/theorems/361c2121-8692-429f-a767-68e663280851
-- title:
--   Positive Twist Average: is Pos Tw one
-- statement:
--   The Positive Twist Average construction uses the is Pos Tw one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/PositiveTwistAverage.lean#L120-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/PositiveTwistAverage.lean#L120-L123

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage.isPosTw_one (ψ : AddChar k Circle) (p : ℕ) (π : Representation ℂ (GL n k) P)
    (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ) :
    IsPosTw ψ 1 p π σ b ↔ IsPos ψ p π σ b := by sorry
