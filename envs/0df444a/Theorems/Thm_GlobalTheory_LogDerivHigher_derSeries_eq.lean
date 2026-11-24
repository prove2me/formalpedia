-- Prove2me | Theorems.Thm_GlobalTheory_LogDerivHigher_derSeries_eq
-- name    : GlobalTheory.LogDerivHigher.derSeries_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:18:57.390812+00:00
-- url     : https://prove2.me/theorems/e23a7d69-a9aa-4807-a0f9-fd3208c1b52d
-- title:
--   Log Deriv Higher: der Series eq
-- statement:
--   The Log Deriv Higher construction uses the der Series eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IteratedDerivLogDerivDirichletLViaNearbyZeros.lean#L103-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IteratedDerivLogDerivDirichletLViaNearbyZeros.lean#L103-L117

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

theorem GlobalTheory.LogDerivHigher.derSeries_eq (c : ℕ → ℂ) (k : ℕ) (s : ℂ) :
    LSeries (LSeries.logMul^[k] (c * fun n : ℕ => ((Λ n : ℝ) : ℂ))) s
      = k.factorial * derSeries c k s := by sorry
