-- Prove2me | Theorems.Thm_GlobalTheory_WpFam_hasSum_rows_derivWeierstrassP
-- name    : GlobalTheory.WpFam.hasSum_rows_derivWeierstrassP
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:56:17.850071+00:00
-- url     : https://prove2.me/theorems/298abed8-450f-494c-829a-b9f91e1cc534
-- title:
--   Wp Fam: has Sum rows deriv Weierstrass P
-- statement:
--   The Wp Fam construction uses the has Sum rows deriv Weierstrass P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumRowsInvCubeDerivWeierstrassP.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumRowsInvCubeDerivWeierstrassP.lean#L29-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumRowsInvCubeDerivWeierstrassP
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
open GlobalTheory GlobalTheory.WpFam

theorem GlobalTheory.WpFam.hasSum_rows_derivWeierstrassP : ∀ (τ : ℍ) (z : ℂ), HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z + n * (τ : ℂ) + m) ^ 3) (-(1 / 2) * (tauPair τ).derivWeierstrassP z) := by sorry
