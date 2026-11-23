-- Prove2me | Theorems.Thm_GlobalTheory_SliceOp_clm_sup_bound
-- name    : GlobalTheory.SliceOp.clm_sup_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:14.718104+00:00
-- url     : https://prove2.me/theorems/a776c674-e8fe-4a9f-a709-00c6a8da92b2
-- title:
--   Slice Op: clm sup bound
-- statement:
--   The Slice Op construction uses the clm sup bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClmSupBound.lean#L28-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClmSupBound.lean#L28-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SliceSchwartz
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.SliceOp
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem GlobalTheory.SliceOp.clm_sup_bound {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : SchwartzMap X ℂ →L[ℂ] SchwartzMap Y ℂ) (s : Finset (ℕ × ℕ)) :
    ∃ (s' : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ f : SchwartzMap X ℂ,
      s.sup (schwartzSeminormFamily ℂ Y ℂ) (T f) ≤ C * s'.sup (schwartzSeminormFamily ℂ X ℂ) f := by sorry
