-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_Inf0_RealBox_continuous_gaussR
-- name    : GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.continuous_gaussR
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:21:22.410183+00:00
-- url     : https://prove2.me/theorems/52827229-5d9e-41e3-97b7-fa5de2de4e9b
-- title:
--   Real Box: continuous gauss R
-- statement:
--   The Real Box construction uses the continuous gauss R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuadraticBoxVolumeBound.lean#L47-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuadraticBoxVolumeBound.lean#L47-L52

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

theorem GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.continuous_gaussR [Fintype P] [Fintype ι] (Pm : P → Matrix ι ι ℝ) :
    Continuous (gaussR Pm) := by sorry
