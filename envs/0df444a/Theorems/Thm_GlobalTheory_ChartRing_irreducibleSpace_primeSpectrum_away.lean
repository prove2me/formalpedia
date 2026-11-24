-- Prove2me | Theorems.Thm_GlobalTheory_ChartRing_irreducibleSpace_primeSpectrum_away
-- name    : GlobalTheory.ChartRing.irreducibleSpace_primeSpectrum_away
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:14:38.70034+00:00
-- url     : https://prove2.me/theorems/049ff684-c018-4bce-8e19-f3b8c80ca472
-- title:
--   Chart Ring: irreducible Space prime Spectrum away
-- statement:
--   The Chart Ring construction uses the irreducible Space prime Spectrum away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IrreducibleSpacePrimeSpectrumAway.lean#L221-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IrreducibleSpacePrimeSpectrumAway.lean#L221-L223

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

theorem GlobalTheory.ChartRing.irreducibleSpace_primeSpectrum_away : IrreducibleSpace (PrimeSpectrum S) := by sorry
