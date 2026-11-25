-- Prove2me | Theorems.Thm_GlobalTheory_CycFr_derivative_bin
-- name    : GlobalTheory.CycFr.derivative_bin
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:01:56.528262+00:00
-- url     : https://prove2.me/theorems/a5262fba-7b58-4386-ad01-3f9766604de4
-- title:
--   Cyc Fr: derivative bin
-- statement:
--   The Cyc Fr construction uses the derivative bin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L153-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L153-L161

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

theorem GlobalTheory.CycFr.derivative_bin (c : ℤ_[l]) :
    derivative O (_root_.GlobalTheory.CycFr.bin O c) = C (algebraMap ℤ_[l] O c) * _root_.GlobalTheory.CycFr.bin O (c - 1) := by sorry
