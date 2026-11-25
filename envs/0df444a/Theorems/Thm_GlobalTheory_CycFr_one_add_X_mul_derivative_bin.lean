-- Prove2me | Theorems.Thm_GlobalTheory_CycFr_one_add_X_mul_derivative_bin
-- name    : GlobalTheory.CycFr.one_add_X_mul_derivative_bin
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:40:26.77685+00:00
-- url     : https://prove2.me/theorems/a9a88772-7915-455d-947e-29b78015dd40
-- title:
--   Cyc Fr: one add X mul derivative bin
-- statement:
--   The Cyc Fr construction uses the one add X mul derivative bin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L176-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L176-L180

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

theorem GlobalTheory.CycFr.one_add_X_mul_derivative_bin (c : ℤ_[l]) :
    (1 + X : O⟦X⟧) * derivative O (_root_.GlobalTheory.CycFr.bin O c) =
      C (algebraMap ℤ_[l] O c) * _root_.GlobalTheory.CycFr.bin O c := by sorry
