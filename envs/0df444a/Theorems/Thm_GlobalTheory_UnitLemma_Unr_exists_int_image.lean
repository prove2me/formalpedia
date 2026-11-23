-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_exists_int_image
-- name    : GlobalTheory.UnitLemma.Unr.exists_int_image
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:27.565655+00:00
-- url     : https://prove2.me/theorems/e8a598ae-b387-4e6c-a9d6-fa47009672a3
-- title:
--   Unr: exists int image
-- statement:
--   The Unr construction uses the exists int image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemRangeOfValNonneg.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemRangeOfValNonneg.lean#L32-L36

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

theorem GlobalTheory.UnitLemma.Unr.exists_int_image {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E} (hU : IsUnrExt K K' d φ) (a : K.O) :
    ∃ b : K'.O, algebraMap K'.O K'.E b = φ (algebraMap K.O K.E a) := by sorry
