-- Prove2me | Theorems.Thm_GlobalTheory_ChartRing_X_mem_maximalIdeal
-- name    : GlobalTheory.ChartRing.X_mem_maximalIdeal
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:38:03.056846+00:00
-- url     : https://prove2.me/theorems/126bc7ad-384d-448c-85e7-edc4b0a3b9aa
-- title:
--   Chart Ring: X mem maximal Ideal
-- statement:
--   The Chart Ring construction uses the X mem maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsPrincipalIdealRingOfIsLocalization.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsPrincipalIdealRingOfIsLocalization.lean#L21-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IrreducibleSpacePrimeSpectrumAway
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsPrincipalIdealRingOfIsLocalization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries IsLocalRing
noncomputable section
open GlobalTheory GlobalTheory.ChartRing
variable {O : Type*} [CommRing O] [IsLocalRing O]

theorem GlobalTheory.ChartRing.X_mem_maximalIdeal : (X : O⟦X⟧) ∈ maximalIdeal O⟦X⟧ := by sorry
