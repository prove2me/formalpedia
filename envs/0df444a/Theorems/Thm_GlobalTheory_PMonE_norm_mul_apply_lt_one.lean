-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_norm_mul_apply_lt_one
-- name    : GlobalTheory.PMonE.norm_mul_apply_lt_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:40:15.243644+00:00
-- url     : https://prove2.me/theorems/7b21c4aa-3fc8-4d4a-bf28-cf209f56fffe
-- title:
--   PMon E: norm mul apply lt one
-- statement:
--   The PMon E construction uses the norm mul apply lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormalOfInvMul.lean#L46-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormalOfInvMul.lean#L46-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormalOfInvMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PMonE
open GlobalTheory GlobalTheory.PMonE
open Finset

theorem GlobalTheory.PMonE.norm_mul_apply_lt_one {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    (A B : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ i j, ‖B i j‖ < 1) (i j : m) :
    ‖(A * B) i j‖ < 1 := by sorry
