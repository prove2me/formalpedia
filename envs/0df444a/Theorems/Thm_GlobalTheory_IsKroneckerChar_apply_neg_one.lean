-- Prove2me | Theorems.Thm_GlobalTheory_IsKroneckerChar_apply_neg_one
-- name    : GlobalTheory.IsKroneckerChar.apply_neg_one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:21:07.228643+00:00
-- url     : https://prove2.me/theorems/36de6578-deb7-4b39-9bc9-6bc492075e21
-- title:
--   Is Kronecker Char: apply neg one
-- statement:
--   The Is Kronecker Char construction uses the apply neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L416-L429
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L416-L429

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

theorem GlobalTheory.IsKroneckerChar.apply_neg_one (hd : 0 < d) : χ (-1) = -1 := by sorry
