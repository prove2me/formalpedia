-- Prove2me | Theorems.Thm_GlobalTheory_DenseCompl_eq_zero_of_forall_le_exp
-- name    : GlobalTheory.DenseCompl.eq_zero_of_forall_le_exp
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:04:15.393145+00:00
-- url     : https://prove2.me/theorems/7732655f-c2c2-572b-bc7d-f82185c21c67
-- title:
--   Dense Compl: eq zero of forall le exp
-- statement:
--   The Dense Compl construction uses the eq zero of forall le exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/EqZeroOfForallLeExp.lean#L71-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/EqZeroOfForallLeExp.lean#L71-L72

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

theorem GlobalTheory.DenseCompl.eq_zero_of_forall_le_exp {a : ℤᵐ⁰} (h : ∀ n : ℕ, a ≤ exp (-(n : ℤ))) : a = 0 := by sorry
