-- Prove2me | Theorems.Thm_GlobalTheory_ChartRing_isAdicComplete_comap_constantCoeff
-- name    : GlobalTheory.ChartRing.isAdicComplete_comap_constantCoeff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:09:10.553586+00:00
-- url     : https://prove2.me/theorems/89275a46-b79f-4e5c-b1bb-54e256f9dede
-- title:
--   Chart Ring: is Adic Complete comap constant Coeff
-- statement:
--   The Chart Ring construction uses the is Adic Complete comap constant Coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsAdicCompleteComapConstantCoeff.lean#L237-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsAdicCompleteComapConstantCoeff.lean#L237-L239

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsAdicCompleteComapConstantCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open GlobalTheory GlobalTheory.ChartRing
variable {A : Type*} [CommRing A] (I : Ideal A)

theorem GlobalTheory.ChartRing.isAdicComplete_comap_constantCoeff [IsAdicComplete I A] :
    IsAdicComplete (I.comap (constantCoeff (R := A))) A⟦X⟧ := by sorry
