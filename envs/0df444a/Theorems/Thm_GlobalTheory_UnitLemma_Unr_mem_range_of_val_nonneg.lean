-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_mem_range_of_val_nonneg
-- name    : GlobalTheory.UnitLemma.Unr.mem_range_of_val_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:37.889407+00:00
-- url     : https://prove2.me/theorems/e3f39aad-4b1d-4732-b0b6-9dcd4845d3ba
-- title:
--   Unr: mem range of val nonneg
-- statement:
--   The Unr construction uses the mem range of val nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemRangeOfValNonneg.lean#L10-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemRangeOfValNonneg.lean#L10-L20

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

theorem GlobalTheory.UnitLemma.Unr.mem_range_of_val_nonneg (K : UQ) (z : K.E) (h : 0 ≤ val K.O z) :
    ∃ a : K.O, algebraMap K.O K.E a = z := by sorry
