-- Prove2me | Theorems.Thm_GlobalTheory_Hadamard_norm_det_apply_sq_le
-- name    : GlobalTheory.Hadamard.norm_det_apply_sq_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:02:26.632013+00:00
-- url     : https://prove2.me/theorems/3cd6aef2-1544-4790-bff4-9dcc929e36c9
-- title:
--   Hadamard: norm det apply sq le
-- statement:
--   The Hadamard construction uses the norm det apply sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsOrthonormalOfLinearIndependent.lean#L130-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsOrthonormalOfLinearIndependent.lean#L130-L151

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

theorem GlobalTheory.Hadamard.norm_det_apply_sq_le (φ : ι → E →L[𝕜] 𝕜) (x : ι → E) :
    ‖(of fun j k => φ j (x k)).det‖ ^ 2 ≤ RCLike.re (gram 𝕜 x).det * ∏ j, ‖φ j‖ ^ 2 := by sorry
