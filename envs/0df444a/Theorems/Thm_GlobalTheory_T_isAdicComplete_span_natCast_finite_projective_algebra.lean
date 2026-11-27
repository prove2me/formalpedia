-- Prove2me | Theorems.Thm_GlobalTheory_T_isAdicComplete_span_natCast_finite_projective_algebra
-- name    : GlobalTheory.T.isAdicComplete_span_natCast_finite_projective_algebra
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:34:05.558044+00:00
-- url     : https://prove2.me/theorems/d94a629a-6aa6-47fa-b4f4-7f7725c5fe0c
-- title:
--   T: is Adic Complete span nat Cast finite projective algebra
-- statement:
--   The T construction uses the is Adic Complete span nat Cast finite projective algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAdicCompleteSpanNatCastFiniteProjectiveAlgebraStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAdicCompleteSpanNatCastFiniteProjectiveAlgebraStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAdicCompleteSpanNatCastFiniteProjectiveAlgebra
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAdicCompleteSpanNatCastFiniteProjectiveAlgebraStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isAdicComplete_span_natCast_finite_projective_algebra : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Projective O A] [IsAdicComplete (Ideal.span {(p : O)}) O], IsAdicComplete (Ideal.span {(p : A)}) A := by sorry
