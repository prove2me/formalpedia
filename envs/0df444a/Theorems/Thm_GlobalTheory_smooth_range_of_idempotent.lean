-- Prove2me | Theorems.Thm_GlobalTheory_smooth_range_of_idempotent
-- name    : GlobalTheory.smooth_range_of_idempotent
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:20:40.83481+00:00
-- url     : https://prove2.me/theorems/0ee185fe-6415-4ab5-9b56-cd163986312b
-- title:
--   Global Theory: smooth range of idempotent
-- statement:
--   The Global Theory construction uses the smooth range of idempotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothRangeOfIdempotentAlgHom.lean#L36-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothRangeOfIdempotentAlgHom.lean#L36-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothRangeOfIdempotentAlgHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.smooth_range_of_idempotent : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.Smooth R A] (e : A →ₐ[R] A), (∀ x, e (e x) = e x) → Algebra.Smooth R e.range := by sorry
