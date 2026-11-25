-- Prove2me | Theorems.Thm_GlobalTheory_T_isAlgebraic_of_isAlgebraic_over_algebraic_subring
-- name    : GlobalTheory.T.isAlgebraic_of_isAlgebraic_over_algebraic_subring
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:33:38.237547+00:00
-- url     : https://prove2.me/theorems/83233a6b-2a91-5acc-a972-e13ca484f137
-- title:
--   T: is Algebraic of is Algebraic over algebraic subring
-- statement:
--   The T construction uses the is Algebraic of is Algebraic over algebraic subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAlgebraicOfSubringIsAlgebraicStatement.lean#L5-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAlgebraicOfSubringIsAlgebraicStatement.lean#L5-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAlgebraicOfSubringIsAlgebraic
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAlgebraicOfSubringIsAlgebraicStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isAlgebraic_of_isAlgebraic_over_algebraic_subring : ∀ {L : Type} [Field L] [Algebra ℂ L] (S : Subalgebra ℂ L) (B : Subring L) (z : L),
  (∀ b ∈ B, IsAlgebraic S b) → IsAlgebraic B z → IsAlgebraic S z := by sorry
