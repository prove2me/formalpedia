-- Prove2me | Theorems.Thm_GlobalTheory_CommSep_commute_aeval_of_commute
-- name    : GlobalTheory.CommSep.commute_aeval_of_commute
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:56.829796+00:00
-- url     : https://prove2.me/theorems/28b5253b-5cda-48ec-ba01-2b3b344637d5
-- title:
--   Comm Sep: commute aeval of commute
-- statement:
--   The Comm Sep construction uses the commute aeval of commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixCommuteOfCommuteSeparableCharpoly.lean#L8-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixCommuteOfCommuteSeparableCharpoly.lean#L8-L14

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

theorem GlobalTheory.CommSep.commute_aeval_of_commute {E : Type} [Field E] {r : ℕ} {m A : Matrix (Fin r) (Fin r) E}
    (h : Commute m A) (p : E[X]) : Commute m (aeval A p) := by sorry
