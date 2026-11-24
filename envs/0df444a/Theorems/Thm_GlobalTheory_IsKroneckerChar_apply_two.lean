-- Prove2me | Theorems.Thm_GlobalTheory_IsKroneckerChar_apply_two
-- name    : GlobalTheory.IsKroneckerChar.apply_two
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:21:26.467487+00:00
-- url     : https://prove2.me/theorems/1591337b-b72c-4194-be43-0fdb3e532ebf
-- title:
--   Is Kronecker Char: apply two
-- statement:
--   The Is Kronecker Char construction uses the apply two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L396-L414
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L396-L414

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped NumberTheorySymbols
open GlobalTheory
open QuadraticZeta
open GlobalTheory.IsKroneckerChar
variable {d : ℕ} {χ : DirichletCharacter ℂ d} (hχ : IsKroneckerChar χ)
include hχ

theorem GlobalTheory.IsKroneckerChar.apply_two (h4 : d % 4 ≠ 1) : χ 2 = (ZMod.χ₈ ((-(d : ℤ) : ℤ) : ZMod 8) : ℤ) := by sorry
