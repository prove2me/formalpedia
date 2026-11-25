-- Prove2me | Theorems.Thm_GlobalTheory_CycFr_dvd_act_sub
-- name    : GlobalTheory.CycFr.dvd_act_sub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:03:18.064912+00:00
-- url     : https://prove2.me/theorems/8dc716bb-5287-52f6-ade9-9485ab0f0040
-- title:
--   Cyc Fr: dvd act sub
-- statement:
--   The Cyc Fr construction uses the dvd act sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L374-L380
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L374-L380

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddXMulDerivativeBin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open GlobalTheory GlobalTheory.CycFr
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
variable {O}
variable [IsDomain O] [CharZero O]
open PowerSeries
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
variable {O}
variable [IsDomain O] [CharZero O]

theorem GlobalTheory.CycFr.dvd_act_sub [IsNoetherianRing O] (k : ℕ) (c d : ℤ_[l]) (h : (l : ℤ_[l]) ^ k ∣ c - d)
    (a : O⟦X⟧) : (1 + X : O⟦X⟧) ^ l ^ k - 1 ∣ _root_.GlobalTheory.CycFr.act O c a - _root_.GlobalTheory.CycFr.act O d a := by sorry
