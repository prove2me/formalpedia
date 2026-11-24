-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_norm_one_apply_le
-- name    : GlobalTheory.PMonE.norm_one_apply_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:40:10.228256+00:00
-- url     : https://prove2.me/theorems/0b7c3373-83ec-4db2-83c4-48acdaeae82d
-- title:
--   PMon E: norm one apply le
-- statement:
--   The PMon E construction uses the norm one apply le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemIntegralSurjectivityOfOne.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemIntegralSurjectivityOfOne.lean#L18-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemIntegralSurjectivityOfOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset Matrix
variable {F : Type*} [NormedField F] {m : Type*} [Fintype m] [DecidableEq m]
omit [Fintype m]

theorem GlobalTheory.PMonE.norm_one_apply_le (i j : m) : ‖(1 : Matrix m m F) i j‖ ≤ 1 := by sorry
