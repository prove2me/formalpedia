-- Prove2me | Theorems.Thm_GlobalTheory_T_mdifferentiable_and_isBoundedAtImInfty_of_hasQ
-- name    : GlobalTheory.T.mdifferentiable_and_isBoundedAtImInfty_of_hasQ
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:35:16.852195+00:00
-- url     : https://prove2.me/theorems/52d54295-b379-421e-984f-3248dd63d496
-- title:
--   T: mdifferentiable and is Bounded At Im Infty of has Q
-- statement:
--   The T construction uses the mdifferentiable and is Bounded At Im Infty of has Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQMdifferentiableAndIsBoundedAtImInftyStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQMdifferentiableAndIsBoundedAtImInftyStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQMdifferentiableAndIsBoundedAtImInfty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQMdifferentiableAndIsBoundedAtImInftyStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.mdifferentiable_and_isBoundedAtImInfty_of_hasQ : ∀ (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ), 0 < N → HasQ N f a → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧ UpperHalfPlane.IsBoundedAtImInfty f := by sorry
