-- Prove2me | Theorems.Thm_GlobalTheory_T_isUnit_of_isUnit_mul_comul_eq_tmul
-- name    : GlobalTheory.T.isUnit_of_isUnit_mul_comul_eq_tmul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:34:20.196805+00:00
-- url     : https://prove2.me/theorems/9cd8c137-f652-5d97-980d-23ccfa474932
-- title:
--   T: is Unit of is Unit mul comul eq tmul
-- statement:
--   The T construction uses the is Unit of is Unit mul comul eq tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsUnitOfUnitMulComulEqTmulSelfStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsUnitOfUnitMulComulEqTmulSelfStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOfUnitMulComulEqTmulSelf
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOfUnitMulComulEqTmulSelfStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isUnit_of_isUnit_mul_comul_eq_tmul : ∀ (K H : Type) [Field K] [CommRing H] [HopfAlgebra K H] (c : H ⊗[K] H), IsUnit c → ∀ u : H, u ≠ 0 → c * Coalgebra.comul (R := K) u = u ⊗ₜ[K] u → IsUnit u := by sorry
