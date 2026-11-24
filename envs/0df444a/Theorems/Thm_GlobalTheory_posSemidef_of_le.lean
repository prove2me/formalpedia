-- Prove2me | Theorems.Thm_GlobalTheory_posSemidef_of_le
-- name    : GlobalTheory.posSemidef_of_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:14:10.421897+00:00
-- url     : https://prove2.me/theorems/6c029fc2-1553-4a45-8be6-432a6b92899e
-- title:
--   Global Theory: pos Semidef of le
-- statement:
--   The Global Theory construction uses the pos Semidef of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/StarInvMulVecDotProductMulVecInvMulVec.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/StarInvMulVecDotProductMulVecInvMulVec.lean#L25-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_OneLeDetOneAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder MatrixOrder
open GlobalTheory
variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]
omit [Fintype n]

theorem GlobalTheory.posSemidef_of_le {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (h : A ≤ B) : B.PosSemidef := by sorry
