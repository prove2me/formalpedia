-- Prove2me | Theorems.Thm_GlobalTheory_ChartRing_order_map_algebraMap
-- name    : GlobalTheory.ChartRing.order_map_algebraMap
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:14:40.588379+00:00
-- url     : https://prove2.me/theorems/f10b8bc5-c9b8-4e2a-a9cd-7a07b3276891
-- title:
--   Chart Ring: order map algebra Map
-- statement:
--   The Chart Ring construction uses the order map algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IrreducibleSpacePrimeSpectrumAway.lean#L123-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IrreducibleSpacePrimeSpectrumAway.lean#L123-L124

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

theorem GlobalTheory.ChartRing.order_map_algebraMap (f : O⟦X⟧) : (f.map (algebraMap O K)).order = f.order := by sorry
