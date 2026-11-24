-- Prove2me | Theorems.Thm_GlobalTheory_Hadamard_gram_sum_smul
-- name    : GlobalTheory.Hadamard.gram_sum_smul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:02:21.8697+00:00
-- url     : https://prove2.me/theorems/19d6664a-9048-479e-894d-566ec2b6c4ad
-- title:
--   Hadamard: gram sum smul
-- statement:
--   The Hadamard construction uses the gram sum smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsOrthonormalOfLinearIndependent.lean#L62-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsOrthonormalOfLinearIndependent.lean#L62-L67

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

theorem GlobalTheory.Hadamard.gram_sum_smul [Fintype κ] (e : ι → E) (m : Matrix ι κ 𝕜) :
    gram 𝕜 (fun j => ∑ i, m i j • e i) = mᴴ * gram 𝕜 e * m := by sorry
