-- Prove2me | Theorems.Thm_GlobalTheory_UnitWitt_conjTranspose_vecMulVec_self
-- name    : GlobalTheory.UnitWitt.conjTranspose_vecMulVec_self
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:39:11.166804+00:00
-- url     : https://prove2.me/theorems/ded53172-d125-4581-bac6-a4096cf0dee7
-- title:
--   Unit Witt: conj Transpose vec Mul Vec self
-- statement:
--   The Unit Witt construction uses the conj Transpose vec Mul Vec self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ConjTransposeVecMulVecSelf.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ConjTransposeVecMulVecSelf.lean#L12-L14

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjTransposeVecMulVecSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.UnitWitt
variable {E : Type} [Field E] [StarRing E] {r : ℕ}

theorem GlobalTheory.UnitWitt.conjTranspose_vecMulVec_self (w : Fin r → E) : (vecMulVec w (star w))ᴴ = vecMulVec w (star w) := by sorry
