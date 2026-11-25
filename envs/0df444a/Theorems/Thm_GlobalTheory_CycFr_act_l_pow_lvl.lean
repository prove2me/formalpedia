-- Prove2me | Theorems.Thm_GlobalTheory_CycFr_act_l_pow_lvl
-- name    : GlobalTheory.CycFr.act_l_pow_lvl
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:03:25.469804+00:00
-- url     : https://prove2.me/theorems/a4366433-410f-4ded-a6a4-c560893eb725
-- title:
--   Cyc Fr: act l pow lvl
-- statement:
--   The Cyc Fr construction uses the act l pow lvl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L297-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L297-L302

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

theorem GlobalTheory.CycFr.act_l_pow_lvl (k : ℕ) : _root_.GlobalTheory.CycFr.act O ((l : ℤ_[l]) ^ k) (_root_.GlobalTheory.CycFr.lvl l O 0) = _root_.GlobalTheory.CycFr.lvl l O k := by sorry
