-- Prove2me | Theorems.Thm_GlobalTheory_Hadamard_norm_det_sq_le_prod_row
-- name    : GlobalTheory.Hadamard.norm_det_sq_le_prod_row
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:02:20.271809+00:00
-- url     : https://prove2.me/theorems/07d95b8c-7e61-444f-b36f-1aba681d8b11
-- title:
--   Hadamard: norm det sq le prod row
-- statement:
--   The Hadamard construction uses the norm det sq le prod row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsOrthonormalOfLinearIndependent.lean#L49-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsOrthonormalOfLinearIndependent.lean#L49-L52

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

theorem GlobalTheory.Hadamard.norm_det_sq_le_prod_row (A : Matrix ι ι 𝕜) :
    ‖A.det‖ ^ 2 ≤ ∏ i, ∑ j, ‖A i j‖ ^ 2 := by sorry
