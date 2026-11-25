-- Prove2me | Theorems.Thm_GlobalTheory_CycFr_act_mul
-- name    : GlobalTheory.CycFr.act_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:40:29.643802+00:00
-- url     : https://prove2.me/theorems/23b1be3b-88fd-4745-864e-f1590fd96fba
-- title:
--   Cyc Fr: act mul
-- statement:
--   The Cyc Fr construction uses the act mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L247-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L247-L254

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

theorem GlobalTheory.CycFr.act_mul (c d : ℤ_[l]) (a : O⟦X⟧) : _root_.GlobalTheory.CycFr.act O (c * d) a = _root_.GlobalTheory.CycFr.act O c (_root_.GlobalTheory.CycFr.act O d a) := by sorry
