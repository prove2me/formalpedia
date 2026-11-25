-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_primitive_addChar_involution_invariant
-- name    : GlobalTheory.T.exists_primitive_addChar_involution_invariant
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:45:20.715312+00:00
-- url     : https://prove2.me/theorems/98a8db54-3856-4e57-aab6-d35b453bfd95
-- title:
--   T: exists primitive add Char involution invariant
-- statement:
--   The T construction uses the exists primitive add Char involution invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsPrimitiveAddCharInvolutionInvariantStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsPrimitiveAddCharInvolutionInvariantStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPrimitiveAddCharInvolutionInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPrimitiveAddCharInvolutionInvariantStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_primitive_addChar_involution_invariant : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∃ χ : AddChar B ℂ, χ.IsPrimitive ∧ ∀ u, χ (c u) = χ u := by sorry
