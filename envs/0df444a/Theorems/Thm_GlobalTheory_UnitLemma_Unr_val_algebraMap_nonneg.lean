-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_val_algebraMap_nonneg
-- name    : GlobalTheory.UnitLemma.Unr.val_algebraMap_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:15.041971+00:00
-- url     : https://prove2.me/theorems/a01d096f-eafe-4887-9e4e-a41b45273a23
-- title:
--   Unr: val algebra Map nonneg
-- statement:
--   The Unr construction uses the val algebra Map nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemRangeOfValNonneg.lean#L22-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemRangeOfValNonneg.lean#L22-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma

theorem GlobalTheory.UnitLemma.Unr.val_algebraMap_nonneg (K : UQ) (a : K.O) : 0 ≤ val K.O (algebraMap K.O K.E a) := by sorry
