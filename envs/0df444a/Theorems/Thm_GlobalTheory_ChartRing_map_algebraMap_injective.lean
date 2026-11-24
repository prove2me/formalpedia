-- Prove2me | Theorems.Thm_GlobalTheory_ChartRing_map_algebraMap_injective
-- name    : GlobalTheory.ChartRing.map_algebraMap_injective
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:15:05.911159+00:00
-- url     : https://prove2.me/theorems/68ff50cc-aa46-403e-b22e-6f75947cdeae
-- title:
--   Chart Ring: map algebra Map injective
-- statement:
--   The Chart Ring construction uses the map algebra Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IrreducibleSpacePrimeSpectrumAway.lean#L118-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IrreducibleSpacePrimeSpectrumAway.lean#L118-L120

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
variable {O : Type*} [CommRing O] [IsDomain O] (K : Type*) [Field K] [Algebra O K]
  [IsFractionRing O K]
omit [IsDomain O]

theorem GlobalTheory.ChartRing.map_algebraMap_injective :
    Function.Injective (PowerSeries.map (algebraMap O K) : O⟦X⟧ →+* K⟦X⟧) := by sorry
