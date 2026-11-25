-- Prove2me | Theorems.Thm_GlobalTheory_T_smooth_range_of_idempotent_algHom
-- name    : GlobalTheory.T.smooth_range_of_idempotent_algHom
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:37:42.246828+00:00
-- url     : https://prove2.me/theorems/627182dc-c45b-5352-b65a-f8ce787dd252
-- title:
--   T: smooth range of idempotent alg Hom
-- statement:
--   The T construction uses the smooth range of idempotent alg Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothRangeOfIdempotentAlgHomStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothRangeOfIdempotentAlgHomStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothRangeOfIdempotentAlgHom
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothRangeOfIdempotentAlgHomStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.smooth_range_of_idempotent_algHom : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.Smooth R A] (e : A →ₐ[R] A), (∀ x, e (e x) = e x) → Algebra.Smooth R e.range := by sorry
