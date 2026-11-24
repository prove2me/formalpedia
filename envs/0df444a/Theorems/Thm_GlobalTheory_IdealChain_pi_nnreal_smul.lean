-- Prove2me | Theorems.Thm_GlobalTheory_IdealChain_pi_nnreal_smul
-- name    : GlobalTheory.IdealChain.pi_nnreal_smul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:05:39.417211+00:00
-- url     : https://prove2.me/theorems/71db9707-d356-4c64-b0c3-cf92bb2a63b0
-- title:
--   Ideal Chain: pi nnreal smul
-- statement:
--   The Ideal Chain construction uses the pi nnreal smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarMeasurePiChangeConstant.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarMeasurePiChangeConstant.lean#L9-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NabsDetEqOfActEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarMeasurePiChangeConstant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical
open GlobalTheory GlobalTheory.IdealChain

theorem GlobalTheory.IdealChain.pi_nnreal_smul {ι X : Type} [Fintype ι] [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] (c : NNReal) :
    (Measure.pi fun _ : ι => c • μ) = (c ^ Fintype.card ι) • Measure.pi fun _ : ι => μ := by sorry
