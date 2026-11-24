-- Prove2me | Theorems.Thm_GlobalTheory_ChartRing_isHausdorff_comap_constantCoeff
-- name    : GlobalTheory.ChartRing.isHausdorff_comap_constantCoeff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:09:09.686554+00:00
-- url     : https://prove2.me/theorems/37b874eb-b083-4716-9ace-9f13ef0b5c1d
-- title:
--   Chart Ring: is Hausdorff comap constant Coeff
-- statement:
--   The Chart Ring construction uses the is Hausdorff comap constant Coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsAdicCompleteComapConstantCoeff.lean#L208-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsAdicCompleteComapConstantCoeff.lean#L208-L216

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

theorem GlobalTheory.ChartRing.isHausdorff_comap_constantCoeff [IsHausdorff I A] :
    IsHausdorff (I.comap (constantCoeff (R := A))) A⟦X⟧ := by sorry
