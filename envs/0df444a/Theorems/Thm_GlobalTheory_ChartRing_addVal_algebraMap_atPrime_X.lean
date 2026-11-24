-- Prove2me | Theorems.Thm_GlobalTheory_ChartRing_addVal_algebraMap_atPrime_X
-- name    : GlobalTheory.ChartRing.addVal_algebraMap_atPrime_X
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:14:33.631958+00:00
-- url     : https://prove2.me/theorems/52528d47-516e-44c4-adb7-a02bcb3c57ca
-- title:
--   Chart Ring: add Val algebra Map at Prime X
-- statement:
--   The Chart Ring construction uses the add Val algebra Map at Prime X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IrreducibleSpacePrimeSpectrumAway.lean#L95-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IrreducibleSpacePrimeSpectrumAway.lean#L95-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsAdicCompleteComapConstantCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IrreducibleSpacePrimeSpectrumAway
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
variable {O : Type*} [CommRing O] [IsDomain O]
variable (S : Type*) [CommRing S] [Algebra O⟦X⟧ S]
  [IsLocalization.AtPrime S (Ideal.span {X} : Ideal O⟦X⟧)]

theorem GlobalTheory.ChartRing.addVal_algebraMap_atPrime_X [IsDomain S] [IsDiscreteValuationRing S] (f : O⟦X⟧) :
    IsDiscreteValuationRing.addVal S (algebraMap O⟦X⟧ S f) = f.order := by sorry
