-- Prove2me | Theorems.Thm_GlobalTheory_ChartRing_algebraMap_X_pow_dvd_iff
-- name    : GlobalTheory.ChartRing.algebraMap_X_pow_dvd_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:14:45.673797+00:00
-- url     : https://prove2.me/theorems/072703ef-884d-49f1-afab-60ad231c4e54
-- title:
--   Chart Ring: algebra Map X pow dvd iff
-- statement:
--   The Chart Ring construction uses the algebra Map X pow dvd iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IrreducibleSpacePrimeSpectrumAway.lean#L24-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IrreducibleSpacePrimeSpectrumAway.lean#L24-L34

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

theorem GlobalTheory.ChartRing.algebraMap_X_pow_dvd_iff (M : Submonoid O⟦X⟧) (hM : ∀ m ∈ M, constantCoeff m ≠ 0)
    (S : Type*) [CommRing S] [Algebra O⟦X⟧ S] [IsLocalization M S] (a : ℕ) (f : O⟦X⟧) :
    algebraMap O⟦X⟧ S X ^ a ∣ algebraMap O⟦X⟧ S f ↔ X ^ a ∣ f := by sorry
