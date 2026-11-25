-- Prove2me | Theorems.Thm_GlobalTheory_CycFr_mul_lvl
-- name    : GlobalTheory.CycFr.mul_lvl
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:03:19.643729+00:00
-- url     : https://prove2.me/theorems/1ac4c963-b24e-524c-8b10-c39328bbafe2
-- title:
--   Cyc Fr: mul lvl
-- statement:
--   The Cyc Fr construction uses the mul lvl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L288-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L288-L290

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
omit [Fact l.Prime] [Algebra ℤ_[l] O] [IsDomain O] [CharZero O]

theorem GlobalTheory.CycFr.mul_lvl (k : ℕ) :
    ((1 + X : O⟦X⟧) ^ l ^ k - 1) * _root_.GlobalTheory.CycFr.lvl l O k = (1 + X) ^ l ^ (k + 1) - 1 := by sorry
