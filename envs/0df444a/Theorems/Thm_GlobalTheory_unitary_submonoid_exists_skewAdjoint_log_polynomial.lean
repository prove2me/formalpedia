-- Prove2me | Theorems.Thm_GlobalTheory_unitary_submonoid_exists_skewAdjoint_log_polynomial
-- name    : GlobalTheory.unitary_submonoid_exists_skewAdjoint_log_polynomial
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:24:20.417083+00:00
-- url     : https://prove2.me/theorems/5902a647-3965-41cd-95cc-c6067b477127
-- title:
--   Global Theory: unitary submonoid exists skew Adjoint log polynomial
-- statement:
--   The Global Theory construction uses the unitary submonoid exists skew Adjoint log polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryExistsSkewLog.lean#L8-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryExistsSkewLog.lean#L8-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryExistsSkewLog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
open scoped Matrix.Norms.L2Operator

theorem GlobalTheory.unitary_submonoid_exists_skewAdjoint_log_polynomial (n : ℕ) (k : Matrix (Fin n) (Fin n) ℂ)
    (hk : k ∈ unitary (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ (X : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ),
      star X = -X ∧ NormedSpace.exp X = k ∧ X = Polynomial.aeval k p := by sorry
