-- Prove2me | Theorems.Thm_GlobalTheory_LogDerivHigher_hasDerivAt_pole
-- name    : GlobalTheory.LogDerivHigher.hasDerivAt_pole
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:18:52.901804+00:00
-- url     : https://prove2.me/theorems/62d728af-fe64-46b1-90d6-97f5154c5570
-- title:
--   Log Deriv Higher: has Deriv At pole
-- statement:
--   The Log Deriv Higher construction uses the has Deriv At pole property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IteratedDerivLogDerivDirichletLViaNearbyZeros.lean#L62-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IteratedDerivLogDerivDirichletLViaNearbyZeros.lean#L62-L71

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

theorem GlobalTheory.LogDerivHigher.hasDerivAt_pole (c w s : ℂ) (k : ℕ) (h : s ≠ w) :
    HasDerivAt (fun z => c / (z - w) ^ (k + 1)) (-((k + 1 : ℕ) : ℂ) * (c / (s - w) ^ (k + 1 + 1))) s := by sorry
