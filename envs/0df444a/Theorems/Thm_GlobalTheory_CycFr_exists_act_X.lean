-- Prove2me | Theorems.Thm_GlobalTheory_CycFr_exists_act_X
-- name    : GlobalTheory.CycFr.exists_act_X
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:03:48.083249+00:00
-- url     : https://prove2.me/theorems/0894fb87-71e6-47c4-adfa-8346c8f51be3
-- title:
--   Cyc Fr: exists act X
-- statement:
--   The Cyc Fr construction uses the exists act X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L141-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L141-L148

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

theorem GlobalTheory.CycFr.exists_act_X (c : ℤ_[l]) :
    ∃ v : O⟦X⟧, _root_.GlobalTheory.CycFr.act O c X = X * v ∧ constantCoeff v = algebraMap ℤ_[l] O c := by sorry
