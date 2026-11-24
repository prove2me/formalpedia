-- Prove2me | Theorems.Thm_GlobalTheory_Hadamard_det_gram_comp_equiv
-- name    : GlobalTheory.Hadamard.det_gram_comp_equiv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:02:18.138138+00:00
-- url     : https://prove2.me/theorems/898d99ea-e624-49b1-b8e8-ffedd070bf32
-- title:
--   Hadamard: det gram comp equiv
-- statement:
--   The Hadamard construction uses the det gram comp equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsOrthonormalOfLinearIndependent.lean#L111-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsOrthonormalOfLinearIndependent.lean#L111-L113

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
omit [DecidableEq ι]

theorem GlobalTheory.Hadamard.det_gram_comp_equiv [DecidableEq ι] (x : ι → E) (σ : κ ≃ ι) :
    (gram 𝕜 (x ∘ σ)).det = (gram 𝕜 x).det := by sorry
