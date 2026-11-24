-- Prove2me | Theorems.Thm_GlobalTheory_SliceWeight_pow_norm_mul_seminorm_sliceR_le
-- name    : GlobalTheory.SliceWeight.pow_norm_mul_seminorm_sliceR_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:44.600071+00:00
-- url     : https://prove2.me/theorems/fc1a7c5e-87b0-4a01-9922-3d72dd7d438c
-- title:
--   Slice Weight: pow norm mul seminorm slice R le
-- statement:
--   The Slice Weight construction uses the pow norm mul seminorm slice R le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PowNormMulSeminormSliceRLe.lean#L47-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PowNormMulSeminormSliceRLe.lean#L47-L67

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

theorem GlobalTheory.SliceWeight.pow_norm_mul_seminorm_sliceR_le (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (κ κ' : Type) [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (a k n : ℕ) (x : κ → V) :
    ‖x‖ ^ a * SchwartzMap.seminorm ℂ k n (sliceR f x) ≤ SchwartzMap.seminorm ℂ (a + k) n f := by sorry
