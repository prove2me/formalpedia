-- Prove2me | Theorems.Thm_GlobalTheory_JR_NormalFormL_vecMul_Bm
-- name    : GlobalTheory.JR.NormalFormL.vecMul_Bm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:34:26.979994+00:00
-- url     : https://prove2.me/theorems/0d9f341f-67c3-46b8-8d53-68b877abcf53
-- title:
--   Normal Form L: vec Mul Bm
-- statement:
--   The Normal Form L construction uses the vec Mul Bm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisBorderedMatrixNormalFormInvariants.lean#L177-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisBorderedMatrixNormalFormInvariants.lean#L177-L179

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.NormalFormL
variable {k : Type} [Field k] {r : ℕ}

theorem GlobalTheory.JR.NormalFormL.vecMul_Bm (Y : Gl r k) : Y.2.2.1 ᵥ* Bm Y = (inv Y).2.1 := by sorry
