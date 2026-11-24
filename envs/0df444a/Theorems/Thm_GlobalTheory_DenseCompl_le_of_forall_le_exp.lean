-- Prove2me | Theorems.Thm_GlobalTheory_DenseCompl_le_of_forall_le_exp
-- name    : GlobalTheory.DenseCompl.le_of_forall_le_exp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:16:05.986886+00:00
-- url     : https://prove2.me/theorems/943d75f8-3b03-4811-becd-757ffcc6fd0c
-- title:
--   Dense Compl: le of forall le exp
-- statement:
--   The Dense Compl construction uses the le of forall le exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/EqZeroOfForallLeExp.lean#L54-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/EqZeroOfForallLeExp.lean#L54-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ContinuousOfValuationEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EqZeroOfForallLeExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open WithZero
open GlobalTheory GlobalTheory.DenseCompl

theorem GlobalTheory.DenseCompl.le_of_forall_le_exp {a b : ℤᵐ⁰} (hb : b ≤ 1)
    (h : ∀ n : ℕ, b ≤ exp (-(n : ℤ)) → a ≤ exp (-(n : ℤ))) : a ≤ b := by sorry
