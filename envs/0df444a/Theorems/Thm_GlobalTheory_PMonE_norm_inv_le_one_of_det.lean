-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_norm_inv_le_one_of_det
-- name    : GlobalTheory.PMonE.norm_inv_le_one_of_det
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:40:34.675704+00:00
-- url     : https://prove2.me/theorems/6cd61979-0007-4b70-a7e9-df8dc2895c8b
-- title:
--   PMon E: norm inv le one of det
-- statement:
--   The PMon E construction uses the norm inv le one of det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormalOfInvMul.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormalOfInvMul.lean#L32-L36

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

theorem GlobalTheory.PMonE.norm_inv_le_one_of_det {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    [DecidableEq m] (A : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (hd : ‖A.det‖ = 1) (i j : m) :
    ‖A⁻¹ i j‖ ≤ 1 := by sorry
