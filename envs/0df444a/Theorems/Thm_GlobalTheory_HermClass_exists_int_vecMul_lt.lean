-- Prove2me | Theorems.Thm_GlobalTheory_HermClass_exists_int_vecMul_lt
-- name    : GlobalTheory.HermClass.exists_int_vecMul_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:14.098571+00:00
-- url     : https://prove2.me/theorems/e7d7e451-50c4-4740-b638-ff1c7f5aea45
-- title:
--   Herm Class: exists int vec Mul lt
-- statement:
--   The Herm Class construction uses the exists int vec Mul lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsShortOfTraceDet.lean#L8-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsShortOfTraceDet.lean#L8-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MinkowskiLinearForms
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsShortOfTraceDet_f72bcdc76e7ca34f
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermClass
open MeasureTheory Module Submodule NumberField Matrix

theorem GlobalTheory.HermClass.exists_int_vecMul_lt {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : A.det ≠ 0) {t : ℝ} (ht : 0 < t) (h : |A.det| < t ^ Fintype.card ι) :
    ∃ z : ι → ℤ, z ≠ 0 ∧ ∀ j, |∑ i, (z i : ℝ) * A i j| < t := by sorry
