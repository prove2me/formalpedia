-- Prove2me | Theorems.Thm_GlobalTheory_CommSep_commute_of_commute_separable
-- name    : GlobalTheory.CommSep.commute_of_commute_separable
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:51.509358+00:00
-- url     : https://prove2.me/theorems/c689bb12-ea86-4884-9f76-9ec3341c73d9
-- title:
--   Comm Sep: commute of commute separable
-- statement:
--   The Comm Sep construction uses the commute of commute separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixCommuteOfCommuteSeparableCharpoly.lean#L53-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixCommuteOfCommuteSeparableCharpoly.lean#L53-L58

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

theorem GlobalTheory.CommSep.commute_of_commute_separable : ∀ (E : Type) [Field E] (r : ℕ)
    (A₀ : Matrix (Fin r) (Fin r) E), A₀.charpoly.Separable → ∀ m n : Matrix (Fin r) (Fin r) E,
    m * A₀ = A₀ * m → n * A₀ = A₀ * n → m * n = n * m := by sorry
