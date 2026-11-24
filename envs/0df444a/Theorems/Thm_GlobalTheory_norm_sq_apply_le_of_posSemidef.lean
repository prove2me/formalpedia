-- Prove2me | Theorems.Thm_GlobalTheory_norm_sq_apply_le_of_posSemidef
-- name    : GlobalTheory.norm_sq_apply_le_of_posSemidef
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:12:50.449871+00:00
-- url     : https://prove2.me/theorems/3872101f-89f4-4db2-b263-dedaf3ea5b0c
-- title:
--   Global Theory: norm sq apply le of pos Semidef
-- statement:
--   The Global Theory construction uses the norm sq apply le of pos Semidef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/StarInvMulVecDotProductMulVecInvMulVec.lean#L160-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/StarInvMulVecDotProductMulVecInvMulVec.lean#L160-L169

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
variable [DecidableEq n]
omit [Fintype n] [DecidableEq n]

theorem GlobalTheory.norm_sq_apply_le_of_posSemidef {A : Matrix n n 𝕜} (hA : A.PosSemidef) (i j : n) :
    ‖A i j‖ ^ 2 ≤ RCLike.re (A i i) * RCLike.re (A j j) := by sorry
