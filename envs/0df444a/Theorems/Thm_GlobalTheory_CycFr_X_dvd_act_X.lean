-- Prove2me | Theorems.Thm_GlobalTheory_CycFr_X_dvd_act_X
-- name    : GlobalTheory.CycFr.X_dvd_act_X
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:00:22.640437+00:00
-- url     : https://prove2.me/theorems/460802ee-4b56-47ec-b12d-543195b7fd4d
-- title:
--   Cyc Fr: X dvd act X
-- statement:
--   The Cyc Fr construction uses the X dvd act X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L106-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L106-L108

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

theorem GlobalTheory.CycFr.X_dvd_act_X (c : ℤ_[l]) : (X : O⟦X⟧) ∣ _root_.GlobalTheory.CycFr.act O c X := by sorry
