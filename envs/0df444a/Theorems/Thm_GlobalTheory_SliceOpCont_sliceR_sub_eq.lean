-- Prove2me | Theorems.Thm_GlobalTheory_SliceOpCont_sliceR_sub_eq
-- name    : GlobalTheory.SliceOpCont.sliceR_sub_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:14:26.533407+00:00
-- url     : https://prove2.me/theorems/b34e1a2d-1e2b-491b-ba29-30db8ecf47a4
-- title:
--   Slice Op Cont: slice R sub eq
-- statement:
--   The Slice Op Cont construction uses the slice R sub eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SeminormSliceRLe.lean#L22-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SeminormSliceRLe.lean#L22-L32

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

theorem GlobalTheory.SliceOpCont.sliceR_sub_eq {κ κ' : Type} [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ)
    (x x₀ : κ → V) :
    sliceR f x - sliceR f x₀
      = sliceR (SchwartzMap.compSubConstCLM ℂ (-(padL (κ' := κ') (x - x₀))) f - f) x₀ := by sorry
