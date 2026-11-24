-- Prove2me | Theorems.Thm_GlobalTheory_CommSep_aeval_mulVec_eq_krylov
-- name    : GlobalTheory.CommSep.aeval_mulVec_eq_krylov
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:15:33.892337+00:00
-- url     : https://prove2.me/theorems/e7ef0031-ff54-400d-979f-6e54c6f03acb
-- title:
--   Comm Sep: aeval mul Vec eq krylov
-- statement:
--   The Comm Sep construction uses the aeval mul Vec eq krylov property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixCommuteOfCommuteSeparableCharpoly.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixCommuteOfCommuteSeparableCharpoly.lean#L16-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixCommuteOfCommuteSeparableCharpoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory GlobalTheory.CommSep

theorem GlobalTheory.CommSep.aeval_mulVec_eq_krylov {E : Type} [Field E] {r : ℕ} (A : Matrix (Fin r) (Fin r) E)
    (v c : Fin r → E) :
    aeval A (∑ j : Fin r, monomial (j : ℕ) (c j)) *ᵥ v = GlobalTheory.ClassParam.krylov A v *ᵥ c := by sorry
