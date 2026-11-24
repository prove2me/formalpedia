-- Prove2me | Theorems.Thm_GlobalTheory_ChartRing_order_map_of_injective
-- name    : GlobalTheory.ChartRing.order_map_of_injective
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:14:17.404083+00:00
-- url     : https://prove2.me/theorems/d5164e1d-cd2c-49b8-bd10-6cfb72e7484b
-- title:
--   Chart Ring: order map of injective
-- statement:
--   The Chart Ring construction uses the order map of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IrreducibleSpacePrimeSpectrumAway.lean#L112-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IrreducibleSpacePrimeSpectrumAway.lean#L112-L115

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

theorem GlobalTheory.ChartRing.order_map_of_injective {A : Type*} [CommRing A] {φ : O →+* A}
    (hφ : Function.Injective φ) (f : O⟦X⟧) : (f.map φ).order = f.order := by sorry
