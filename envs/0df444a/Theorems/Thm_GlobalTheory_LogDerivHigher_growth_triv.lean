-- Prove2me | Theorems.Thm_GlobalTheory_LogDerivHigher_growth_triv
-- name    : GlobalTheory.LogDerivHigher.growth_triv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:18:52.637315+00:00
-- url     : https://prove2.me/theorems/45fdfa18-cbdb-497c-a506-dae25b633032
-- title:
--   Log Deriv Higher: growth triv
-- statement:
--   The Log Deriv Higher construction uses the growth triv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IteratedDerivLogDerivDirichletLViaNearbyZeros.lean#L119-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IteratedDerivLogDerivDirichletLViaNearbyZeros.lean#L119-L159

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormSubOneMulRiemannZetaLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZeros
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.LogDerivHigher

theorem GlobalTheory.LogDerivHigher.growth_triv : ∃ B : ℝ, 0 < B ∧ ∀ (q : ℕ) [NeZero q] (z : ℂ), -(7 / 4 : ℝ) ≤ z.re →
    ‖LFunctionTrivChar₁ q z‖ ≤ B * (q : ℝ) ^ 5 * (‖z‖ + 2) ^ 5 := by sorry
