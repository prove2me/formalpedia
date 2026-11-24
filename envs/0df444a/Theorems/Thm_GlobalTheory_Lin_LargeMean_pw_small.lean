-- Prove2me | Theorems.Thm_GlobalTheory_Lin_LargeMean_pw_small
-- name    : GlobalTheory.Lin.LargeMean.pw_small
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:06:06.846876+00:00
-- url     : https://prove2.me/theorems/d0105367-e7dd-40e0-8e21-2ec11b339c97
-- title:
--   Large Mean: pw small
-- statement:
--   The Large Mean construction uses the pw small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LargeMeanOfLargeDerivative.lean#L30-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LargeMeanOfLargeDerivative.lean#L30-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsTsumVonMangoldtDivRpowLeDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNonPrimeVonMangoldtDivRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumPrimesIocEqSumIndicator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntervalIntegrableDivOfBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LargeMeanOfLargeDerivative
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
noncomputable section
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.LargeMean

theorem GlobalTheory.Lin.LargeMean.pw_small (K k : ℕ) {u δ : ℝ} (hδ : 0 < δ) (hu : 0 ≤ u) (h : u ≤ δ / 3 * K) (hK : K ≤ k) :
    pw k u ≤ δ ^ k * Real.exp (-(u / 2)) := by sorry
