-- Prove2me | Theorems.Thm_GlobalTheory_PrecompleteOfPowLe_isPrecomplete_of_le_of_pow_le
-- name    : GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:38:53.72227+00:00
-- url     : https://prove2.me/theorems/5d6b67ea-9de9-48ae-96ba-151dd465b186
-- title:
--   Precomplete Of Pow Le: is Precomplete of le of pow le
-- statement:
--   The Precomplete Of Pow Le construction uses the is Precomplete of le of pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsPrecompleteOfLeOfPowLe.lean#L7-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsPrecompleteOfLeOfPowLe.lean#L7-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPrecompleteOfLeOfPowLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PrecompleteOfPowLe
universe u

theorem GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le {A : Type u} [CommRing A] {I J : Ideal A} (hJI : J ≤ I)
    {e : ℕ} (he : I ^ e ≤ J) [hJ : IsPrecomplete J A] : IsPrecomplete I A := by sorry
