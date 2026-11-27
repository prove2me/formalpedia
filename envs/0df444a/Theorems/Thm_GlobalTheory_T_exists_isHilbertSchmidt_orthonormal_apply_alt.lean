-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_isHilbertSchmidt_orthonormal_apply_alt
-- name    : GlobalTheory.T.exists_isHilbertSchmidt_orthonormal_apply_alt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-27T06:05:46.298316+00:00
-- url     : https://prove2.me/theorems/cc7bbffc-ea3b-5e46-833e-07d1d1d95cfc
-- title:
--   T: exists is Hilbert Schmidt orthonormal apply alt
-- statement:
--   The T construction uses the exists is Hilbert Schmidt orthonormal apply alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsIsHilbertSchmidtOrthonormalApplyStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsIsHilbertSchmidtOrthonormalApplyStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsHilbertSchmidtOrthonormalApply
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SplitHeightSummableExpNegAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsHilbertSchmidtOrthonormalApplyStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_isHilbertSchmidt_orthonormal_apply_alt : ∀ (H K : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (J : Type) (u : J → H) (w : J → K), Orthonormal ℂ u → Summable (fun j => ‖w j‖ ^ 2) → ∃ G : H →L[ℂ] K, (∀ j, G (u j) = w j) ∧ (∀ v, (∀ j, inner ℂ (u j) v = 0) → G v = 0) ∧ GlobalTheory.OpTrace.IsHilbertSchmidt G := by sorry
