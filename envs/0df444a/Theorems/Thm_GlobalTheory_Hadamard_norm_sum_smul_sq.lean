-- Prove2me | Theorems.Thm_GlobalTheory_Hadamard_norm_sum_smul_sq
-- name    : GlobalTheory.Hadamard.norm_sum_smul_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:55.509412+00:00
-- url     : https://prove2.me/theorems/859a4016-bd10-4f4c-8c89-57d86d814bdb
-- title:
--   Hadamard: norm sum smul sq
-- statement:
--   The Hadamard construction uses the norm sum smul sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsOrthonormalOfLinearIndependent.lean#L91-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsOrthonormalOfLinearIndependent.lean#L91-L96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsOrthonormalOfLinearIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module
open scoped InnerProductSpace ComplexOrder
open GlobalTheory GlobalTheory.Hadamard
variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
omit [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem GlobalTheory.Hadamard.norm_sum_smul_sq {e : ι → E} (he : Orthonormal 𝕜 e) (c : ι → 𝕜) :
    ‖∑ i, c i • e i‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by sorry
