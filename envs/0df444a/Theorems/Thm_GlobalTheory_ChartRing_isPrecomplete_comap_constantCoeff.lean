-- Prove2me | Theorems.Thm_GlobalTheory_ChartRing_isPrecomplete_comap_constantCoeff
-- name    : GlobalTheory.ChartRing.isPrecomplete_comap_constantCoeff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:09:15.475038+00:00
-- url     : https://prove2.me/theorems/6849c375-90d0-4de0-a3fb-db782ee241eb
-- title:
--   Chart Ring: is Precomplete comap constant Coeff
-- statement:
--   The Chart Ring construction uses the is Precomplete comap constant Coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsAdicCompleteComapConstantCoeff.lean#L218-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsAdicCompleteComapConstantCoeff.lean#L218-L235

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

theorem GlobalTheory.ChartRing.isPrecomplete_comap_constantCoeff [IsPrecomplete I A] :
    IsPrecomplete (I.comap (constantCoeff (R := A))) A⟦X⟧ := by sorry
