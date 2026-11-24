-- Prove2me | Theorems.Thm_GlobalTheory_Hadamard_re_det_gram_le_prod
-- name    : GlobalTheory.Hadamard.re_det_gram_le_prod
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:02:41.746722+00:00
-- url     : https://prove2.me/theorems/907c12c9-73d5-42c6-9dfd-87d10dce16b5
-- title:
--   Hadamard: re det gram le prod
-- statement:
--   The Hadamard construction uses the re det gram le prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsOrthonormalOfLinearIndependent.lean#L98-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsOrthonormalOfLinearIndependent.lean#L98-L107

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

theorem GlobalTheory.Hadamard.re_det_gram_le_prod (x : ι → E) : RCLike.re (gram 𝕜 x).det ≤ ∏ k, ‖x k‖ ^ 2 := by sorry
