-- Prove2me | Theorems.Thm_GlobalTheory_CycFr_act_nat_X
-- name    : GlobalTheory.CycFr.act_nat_X
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:40:16.825547+00:00
-- url     : https://prove2.me/theorems/2f47e80e-8b0e-58e7-a1cd-8c058aefd923
-- title:
--   Cyc Fr: act nat X
-- statement:
--   The Cyc Fr construction uses the act nat X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L280-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L280-L281

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
omit [IsDomain O] [CharZero O]

theorem GlobalTheory.CycFr.act_nat_X (d : ℕ) : _root_.GlobalTheory.CycFr.act O (d : ℤ_[l]) X = (1 + X) ^ d - 1 := by sorry
