-- Prove2me | Theorems.Thm_GlobalTheory_Hadamard_norm_orthonormalBasis_det_le
-- name    : GlobalTheory.Hadamard.norm_orthonormalBasis_det_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:02:23.331908+00:00
-- url     : https://prove2.me/theorems/2e6f405d-d901-4b1e-9f8c-332fea8012dd
-- title:
--   Hadamard: norm orthonormal Basis det le
-- statement:
--   The Hadamard construction uses the norm orthonormal Basis det le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsOrthonormalOfLinearIndependent.lean#L11-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsOrthonormalOfLinearIndependent.lean#L11-L27

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

theorem GlobalTheory.Hadamard.norm_orthonormalBasis_det_le (b : OrthonormalBasis ι 𝕜 E) (x : ι → E) :
    ‖b.toBasis.det x‖ ≤ ∏ k, ‖x k‖ := by sorry
