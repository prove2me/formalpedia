-- Prove2me | Theorems.Thm_GlobalTheory_ChartRing_connectedSpace_primeSpectrum_away
-- name    : GlobalTheory.ChartRing.connectedSpace_primeSpectrum_away
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:14:51.064106+00:00
-- url     : https://prove2.me/theorems/9a21318b-fc1b-4c11-a2b0-a828aa343d8f
-- title:
--   Chart Ring: connected Space prime Spectrum away
-- statement:
--   The Chart Ring construction uses the connected Space prime Spectrum away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IrreducibleSpacePrimeSpectrumAway.lean#L225-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IrreducibleSpacePrimeSpectrumAway.lean#L225-L227

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
open AlgebraicGeometry
universe u
variable {R : Type*} [CommRing R] [IsDomain R] {f : R} (hf : f ≠ 0)
  (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.Away f S]
include hf

theorem GlobalTheory.ChartRing.connectedSpace_primeSpectrum_away : ConnectedSpace (PrimeSpectrum S) := by sorry
