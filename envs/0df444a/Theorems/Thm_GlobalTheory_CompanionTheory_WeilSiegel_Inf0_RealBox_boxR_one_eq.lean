-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_Inf0_RealBox_boxR_one_eq
-- name    : GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.boxR_one_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:21:21.263263+00:00
-- url     : https://prove2.me/theorems/21958365-3b8f-4b85-a1c1-ad9079d457c4
-- title:
--   Real Box: box R one eq
-- statement:
--   The Real Box construction uses the box R one eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuadraticBoxVolumeBound.lean#L54-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuadraticBoxVolumeBound.lean#L54-L58

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoreR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuadraticBoxVolumeBound
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WeilSiegel GlobalTheory.CompanionTheory.WeilSiegel.Inf0 GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox
variable {P ι : Type}

theorem GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.boxR_one_eq [Fintype P] [Fintype ι] :
    boxR (fun _ : P => (1 : ℝ)) = Metric.closedBall (0 : P → ι → ℝ) 1 := by sorry
