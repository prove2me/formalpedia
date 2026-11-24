-- Prove2me | Theorems.Thm_GlobalTheory_ChartRing_algebraMap_injective_away
-- name    : GlobalTheory.ChartRing.algebraMap_injective_away
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:09:39.005286+00:00
-- url     : https://prove2.me/theorems/edde6fd8-bcbc-4d2d-9ac2-ea1ad126fe4f
-- title:
--   Chart Ring: algebra Map injective away
-- statement:
--   The Chart Ring construction uses the algebra Map injective away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IrreducibleSpacePrimeSpectrumAway.lean#L218-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IrreducibleSpacePrimeSpectrumAway.lean#L218-L219

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

theorem GlobalTheory.ChartRing.algebraMap_injective_away : Function.Injective (algebraMap R S) := by sorry
