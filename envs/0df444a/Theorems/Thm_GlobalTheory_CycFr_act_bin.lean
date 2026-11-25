-- Prove2me | Theorems.Thm_GlobalTheory_CycFr_act_bin
-- name    : GlobalTheory.CycFr.act_bin
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:00:31.218518+00:00
-- url     : https://prove2.me/theorems/6f0d664a-f21b-4553-9a8d-2016c730e2d5
-- title:
--   Cyc Fr: act bin
-- statement:
--   The Cyc Fr construction uses the act bin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L220-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L220-L241

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

theorem GlobalTheory.CycFr.act_bin (c d : ℤ_[l]) :
    _root_.GlobalTheory.CycFr.act O c (_root_.GlobalTheory.CycFr.bin O d) =
      _root_.GlobalTheory.CycFr.bin O (c * d) := by sorry
