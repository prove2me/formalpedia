-- Prove2me | Theorems.Thm_GlobalTheory_SliceWeight_iteratedFDeriv_sliceR_norm_le
-- name    : GlobalTheory.SliceWeight.iteratedFDeriv_sliceR_norm_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:18:21.542108+00:00
-- url     : https://prove2.me/theorems/3a74915e-d471-442e-8c47-e39bb36acbb1
-- title:
--   Slice Weight: iterated FDeriv slice R norm le
-- statement:
--   The Slice Weight construction uses the iterated FDeriv slice R norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PowNormMulSeminormSliceRLe.lean#L25-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PowNormMulSeminormSliceRLe.lean#L25-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowNormMulSeminormSliceRLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.SliceWeight
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem GlobalTheory.SliceWeight.iteratedFDeriv_sliceR_norm_le {κ κ' : Type} [Fintype κ] [Fintype κ']
    (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (x : κ → V) (n : ℕ) (y : κ' → V) :
    ‖iteratedFDeriv ℝ n (sliceR f x) y‖ ≤ ‖iteratedFDeriv ℝ n f (Sum.elim x y)‖ := by sorry
