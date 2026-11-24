-- Prove2me | Theorems.Thm_GlobalTheory_UnitValueExistence_norm_det_lt_one
-- name    : GlobalTheory.UnitValueExistence.norm_det_lt_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:39:16.408078+00:00
-- url     : https://prove2.me/theorems/826a24e8-d1fd-4f09-aeca-632765832fe9
-- title:
--   Unit Value Existence: norm det lt one
-- statement:
--   The Unit Value Existence construction uses the norm det lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormOneAddEqOne.lean#L16-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormOneAddEqOne.lean#L16-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormOneAddEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitValueExistence
open Matrix

theorem GlobalTheory.UnitValueExistence.norm_det_lt_one {E : Type} [NormedField E] [IsUltrametricDist E]
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (G : Matrix n n E)
    (h : ∀ i j, ‖G i j‖ < 1) : ‖G.det‖ < 1 := by sorry
