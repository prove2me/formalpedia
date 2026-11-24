-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_perm_of_sum_min_eq_positive_family
-- name    : GlobalTheory.T.exists_perm_of_sum_min_eq_positive_family
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:36:44.135126+00:00
-- url     : https://prove2.me/theorems/d4fa4b44-58f9-46a6-b4c4-d2f6aed00125
-- title:
--   T: exists perm of sum min eq positive family
-- statement:
--   The T construction uses the exists perm of sum min eq positive family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsPermOfSumMinEqPositiveFamilyStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsPermOfSumMinEqPositiveFamilyStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsPermOfSumMinEqPositiveFamily
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsPermOfSumMinEqPositiveFamilyStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_perm_of_sum_min_eq_positive_family : ∀ (d d' : ℕ) (e : Fin d → ℕ) (e' : Fin d' → ℕ), (∀ i, 0 < e i) → (∀ i, 0 < e' i) → (∀ j : ℕ, ∑ i, min j (e i) = ∑ i, min j (e' i)) → ∃ σ : Fin d ≃ Fin d', ∀ i, e' (σ i) = e i := by sorry
