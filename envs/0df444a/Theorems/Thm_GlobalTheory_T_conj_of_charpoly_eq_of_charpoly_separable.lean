-- Prove2me | Theorems.Thm_GlobalTheory_T_conj_of_charpoly_eq_of_charpoly_separable
-- name    : GlobalTheory.T.conj_of_charpoly_eq_of_charpoly_separable
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:31:21.433933+00:00
-- url     : https://prove2.me/theorems/26e1dd77-5fac-4132-ad08-f240af0ffa2b
-- title:
--   T: conj of charpoly eq of charpoly separable
-- statement:
--   The T construction uses the conj of charpoly eq of charpoly separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConjOfCharpolyEqOfCharpolySeparableStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConjOfCharpolyEqOfCharpolySeparableStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjOfCharpolyEqOfCharpolySeparable
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCyclicVectorOfSeparableCharpoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjOfCharpolyEqOfCharpolySeparableStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.conj_of_charpoly_eq_of_charpoly_separable : ∀ (R : Type) [Field R] (m : ℕ) (N U : Matrix (Fin m) (Fin m) R), N.charpoly = U.charpoly → N.charpoly.Separable → ∃ P : GL (Fin m) R, N * P.val = P.val * U := by sorry
