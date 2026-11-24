-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_norm_det_le_one_of_entries
-- name    : GlobalTheory.PMonE.norm_det_le_one_of_entries
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:40:30.997013+00:00
-- url     : https://prove2.me/theorems/1aceeebd-2f0b-410c-b602-9e4d922513d0
-- title:
--   PMon E: norm det le one of entries
-- statement:
--   The PMon E construction uses the norm det le one of entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormalOfInvMul.lean#L10-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormalOfInvMul.lean#L10-L18

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

theorem GlobalTheory.PMonE.norm_det_le_one_of_entries {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    [DecidableEq m] (A : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) : ‖A.det‖ ≤ 1 := by sorry
