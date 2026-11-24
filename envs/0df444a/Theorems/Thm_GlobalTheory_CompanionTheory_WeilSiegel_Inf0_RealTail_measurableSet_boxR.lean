-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_Inf0_RealTail_measurableSet_boxR
-- name    : GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail.measurableSet_boxR
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:23:22.22999+00:00
-- url     : https://prove2.me/theorems/15026a95-dd97-4b72-a734-1a22361ee951
-- title:
--   Real Tail: measurable Set box R
-- statement:
--   The Real Tail construction uses the measurable Set box R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuadraticBoxIntegralSmallBall.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuadraticBoxIntegralSmallBall.lean#L12-L17

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoreR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuadraticBoxIntegralSmallBall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology GlobalTheory.CompanionTheory.WeilSiegel.Inf0
open scoped ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WeilSiegel GlobalTheory.CompanionTheory.WeilSiegel.Inf0 GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail
variable {P ι : Type} [Fintype P] [Fintype ι]

theorem GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail.measurableSet_boxR (t : P → ℝ) : MeasurableSet (boxR t : Set (P → ι → ℝ)) := by sorry
