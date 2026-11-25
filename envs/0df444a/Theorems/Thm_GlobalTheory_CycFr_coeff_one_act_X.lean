-- Prove2me | Theorems.Thm_GlobalTheory_CycFr_coeff_one_act_X
-- name    : GlobalTheory.CycFr.coeff_one_act_X
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:01:24.289311+00:00
-- url     : https://prove2.me/theorems/b6741e10-bb6f-55ba-b12f-69ff7ceccb32
-- title:
--   Cyc Fr: coeff one act X
-- statement:
--   The Cyc Fr construction uses the coeff one act X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L132-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L132-L135

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
open PowerSeries
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
variable {O}

theorem GlobalTheory.CycFr.coeff_one_act_X (c : ℤ_[l]) : coeff 1 (_root_.GlobalTheory.CycFr.act O c X) = algebraMap ℤ_[l] O c := by sorry
