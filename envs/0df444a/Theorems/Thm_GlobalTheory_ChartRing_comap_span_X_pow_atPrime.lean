-- Prove2me | Theorems.Thm_GlobalTheory_ChartRing_comap_span_X_pow_atPrime
-- name    : GlobalTheory.ChartRing.comap_span_X_pow_atPrime
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:14:53.549325+00:00
-- url     : https://prove2.me/theorems/392b6c1a-5bfe-4f63-b7ad-26b8da22cbac
-- title:
--   Chart Ring: comap span X pow at Prime
-- statement:
--   The Chart Ring construction uses the comap span X pow at Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IrreducibleSpacePrimeSpectrumAway.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IrreducibleSpacePrimeSpectrumAway.lean#L43-L47

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

theorem GlobalTheory.ChartRing.comap_span_X_pow_atPrime (a : ℕ) :
    (Ideal.span {algebraMap O⟦X⟧ S X ^ a}).comap (algebraMap O⟦X⟧ S) = Ideal.span {X ^ a} := by sorry
