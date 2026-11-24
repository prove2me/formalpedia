-- Prove2me | Theorems.Thm_GlobalTheory_SliceOpCont_continuous_sliceR
-- name    : GlobalTheory.SliceOpCont.continuous_sliceR
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:14:53.280254+00:00
-- url     : https://prove2.me/theorems/6667e6e3-b3b0-4c38-a926-c79a10a9e15a
-- title:
--   Slice Op Cont: continuous slice R
-- statement:
--   The Slice Op Cont construction uses the continuous slice R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SeminormSliceRLe.lean#L40-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SeminormSliceRLe.lean#L40-L61

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

theorem GlobalTheory.SliceOpCont.continuous_sliceR (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {κ κ' : Type} [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ) :
    Continuous (fun x : κ → V => sliceR f x) := by sorry
