-- Prove2me | Theorems.Thm_GlobalTheory_ChartRing_mem_pow_comap_constantCoeff_iff
-- name    : GlobalTheory.ChartRing.mem_pow_comap_constantCoeff_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:26:52.327901+00:00
-- url     : https://prove2.me/theorems/5406064c-8970-41de-b367-7c8e3fc98344
-- title:
--   Chart Ring: mem pow comap constant Coeff iff
-- statement:
--   The Chart Ring construction uses the mem pow comap constant Coeff iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsAdicCompleteComapConstantCoeff.lean#L170-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsAdicCompleteComapConstantCoeff.lean#L170-L206

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsAdicCompleteComapConstantCoeff
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
variable {A : Type*} [CommRing A] (I : Ideal A)

theorem GlobalTheory.ChartRing.mem_pow_comap_constantCoeff_iff (n : ℕ) (f : A⟦X⟧) :
    f ∈ I.comap (constantCoeff (R := A)) ^ n ↔ ∀ i, coeff i f ∈ I ^ (n - i) := by sorry
