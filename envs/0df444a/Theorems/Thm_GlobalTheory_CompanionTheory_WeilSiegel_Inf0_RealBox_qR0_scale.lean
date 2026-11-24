-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_Inf0_RealBox_qR0_scale
-- name    : GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.qR0_scale
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:22:59.877738+00:00
-- url     : https://prove2.me/theorems/e7f2c317-fc76-412f-a4e9-e5e91a0d69a8
-- title:
--   Real Box: q R0 scale
-- statement:
--   The Real Box construction uses the q R0 scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuadraticBoxVolumeBound.lean#L120-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuadraticBoxVolumeBound.lean#L120-L124

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

theorem GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.qR0_scale [Fintype ι] (A : P → Matrix ι ι ℝ) (t : P → ℝ) (x : P → ι → ℝ) :
    qR0 A (fun w => t w • x w) = fun w => (t w ^ 2) • qR0 A x w := by sorry
