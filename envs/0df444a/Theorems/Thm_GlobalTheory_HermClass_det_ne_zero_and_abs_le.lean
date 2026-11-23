-- Prove2me | Theorems.Thm_GlobalTheory_HermClass_det_ne_zero_and_abs_le
-- name    : GlobalTheory.HermClass.det_ne_zero_and_abs_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:20.789959+00:00
-- url     : https://prove2.me/theorems/08d19b7b-68d0-414e-93df-42eb34ae54c0
-- title:
--   Herm Class: det ne zero and abs le
-- statement:
--   The Herm Class construction uses the det ne zero and abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsShortOfTraceDet.lean#L19-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsShortOfTraceDet.lean#L19-L54

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

theorem GlobalTheory.HermClass.det_ne_zero_and_abs_le {ι : Type} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℚ)
    {M : ℤ} (hM : M ≠ 0)
    (h : ∀ x : ι → ℚ, (∀ j, ∃ m : ℤ, (x ᵥ* T) j = m) → ∀ i, ∃ m : ℤ, M * x i = m) :
    T.det ≠ 0 ∧ |T.det| ≤ |(M : ℚ)| ^ Fintype.card ι := by sorry
