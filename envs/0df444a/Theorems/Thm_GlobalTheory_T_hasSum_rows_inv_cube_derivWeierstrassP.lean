-- Prove2me | Theorems.Thm_GlobalTheory_T_hasSum_rows_inv_cube_derivWeierstrassP
-- name    : GlobalTheory.T.hasSum_rows_inv_cube_derivWeierstrassP
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:44:11.129405+00:00
-- url     : https://prove2.me/theorems/8b43bc41-62c2-49fe-8601-134109f70b64
-- title:
--   T: has Sum rows inv cube deriv Weierstrass P
-- statement:
--   The T construction uses the has Sum rows inv cube deriv Weierstrass P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumRowsInvCubeDerivWeierstrassPStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumRowsInvCubeDerivWeierstrassPStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumRowsInvCubeDerivWeierstrassP
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumRowsInvCubeDerivWeierstrassPStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hasSum_rows_inv_cube_derivWeierstrassP : ∀ (τ : ℍ) (z : ℂ), HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z + n * (τ : ℂ) + m) ^ 3) (-(1 / 2) * (tauPair τ).derivWeierstrassP z) := by sorry
