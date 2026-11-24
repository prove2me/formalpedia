-- Prove2me | Theorems.Thm_GlobalTheory_SliceTaylor_seminorm_slice_taylor_le
-- name    : GlobalTheory.SliceTaylor.seminorm_slice_taylor_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:18:24.317595+00:00
-- url     : https://prove2.me/theorems/3e880efb-ed1c-4943-b659-0266639dfc47
-- title:
--   Slice Taylor: seminorm slice taylor le
-- statement:
--   The Slice Taylor construction uses the seminorm slice taylor le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivPdLe.lean#L63-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivPdLe.lean#L63-L142

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormTranslateSubLineDerivLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivPdLe
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
open GlobalTheory GlobalTheory.SliceTaylor
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem GlobalTheory.SliceTaylor.seminorm_slice_taylor_le (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (κ κ' : Type) [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (k n : ℕ) (x h : κ → V) :
    SchwartzMap.seminorm ℂ k n (sliceR f (x + h) - sliceR f x - sliceR (pd (padL (κ' := κ') h) f) x) ≤
      ‖h‖ ^ 2 * SchwartzMap.seminorm ℂ k (n + 2) f := by sorry
