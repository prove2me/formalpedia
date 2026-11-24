-- Prove2me | Theorems.Thm_GlobalTheory_SliceOpCont_seminorm_sliceR_le
-- name    : GlobalTheory.SliceOpCont.seminorm_sliceR_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:13:46.579182+00:00
-- url     : https://prove2.me/theorems/40995853-a5ed-4d63-890c-cfb5f28ae221
-- title:
--   Slice Op Cont: seminorm slice R le
-- statement:
--   The Slice Op Cont construction uses the seminorm slice R le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SeminormSliceRLe.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SeminormSliceRLe.lean#L34-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTranslationSeminormBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowNormMulSeminormSliceRLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SeminormSliceRLe
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
open GlobalTheory GlobalTheory.SliceOpCont
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem GlobalTheory.SliceOpCont.seminorm_sliceR_le (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {κ κ' : Type} [Fintype κ] [Fintype κ'] (g : SchwartzMap (κ ⊕ κ' → V) ℂ) (x : κ → V) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (sliceR g x) ≤ SchwartzMap.seminorm ℂ k n g := by sorry
