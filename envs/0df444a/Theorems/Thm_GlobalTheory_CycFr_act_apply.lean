-- Prove2me | Theorems.Thm_GlobalTheory_CycFr_act_apply
-- name    : GlobalTheory.CycFr.act_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:00:31.396486+00:00
-- url     : https://prove2.me/theorems/eb4daa3d-1343-466c-b23f-bba2701b0e4f
-- title:
--   Cyc Fr: act apply
-- statement:
--   The Cyc Fr construction uses the act apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L80-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L80-L81

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

theorem GlobalTheory.CycFr.act_apply (c : ℤ_[l]) (a : O⟦X⟧) : _root_.GlobalTheory.CycFr.act O c a = a.subst (_root_.GlobalTheory.CycFr.bin O c - 1) := by sorry
