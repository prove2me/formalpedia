-- Prove2me | Theorems.Thm_GlobalTheory_CommSep_eq_aeval_of_commute_of_separable
-- name    : GlobalTheory.CommSep.eq_aeval_of_commute_of_separable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:07.160467+00:00
-- url     : https://prove2.me/theorems/24fa7052-24cb-4580-b972-bec89eb1cc92
-- title:
--   Comm Sep: eq aeval of commute of separable
-- statement:
--   The Comm Sep construction uses the eq aeval of commute of separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixCommuteOfCommuteSeparableCharpoly.lean#L26-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixCommuteOfCommuteSeparableCharpoly.lean#L26-L51

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

theorem GlobalTheory.CommSep.eq_aeval_of_commute_of_separable {E : Type} [Field E] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) E) (hs : A.charpoly.Separable) (n : Matrix (Fin r) (Fin r) E)
    (hn : n * A = A * n) : ∃ q : E[X], n = aeval A q := by sorry
