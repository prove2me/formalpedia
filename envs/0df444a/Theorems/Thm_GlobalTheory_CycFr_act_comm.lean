-- Prove2me | Theorems.Thm_GlobalTheory_CycFr_act_comm
-- name    : GlobalTheory.CycFr.act_comm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:40:31.690886+00:00
-- url     : https://prove2.me/theorems/2b5156ce-d4d6-4f4a-a37f-c49986a2d350
-- title:
--   Cyc Fr: act comm
-- statement:
--   The Cyc Fr construction uses the act comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L260-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L260-L261

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

theorem GlobalTheory.CycFr.act_comm (c d : ℤ_[l]) (a : O⟦X⟧) : _root_.GlobalTheory.CycFr.act O c (_root_.GlobalTheory.CycFr.act O d a) = _root_.GlobalTheory.CycFr.act O d (_root_.GlobalTheory.CycFr.act O c a) := by sorry
