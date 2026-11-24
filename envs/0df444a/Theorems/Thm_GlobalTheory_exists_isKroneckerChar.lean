-- Prove2me | Theorems.Thm_GlobalTheory_exists_isKroneckerChar
-- name    : GlobalTheory.exists_isKroneckerChar
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:33:04.753098+00:00
-- url     : https://prove2.me/theorems/0070b7a7-a631-4d38-aa6e-7a0bd05df707
-- title:
--   Global Theory: exists is Kronecker Char
-- statement:
--   The Global Theory construction uses the exists is Kronecker Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L453-L497
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L453-L497

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

theorem GlobalTheory.exists_isKroneckerChar {d : ℕ} (hd0 : d ≠ 0) (hd : d % 4 = 0 ∨ d % 4 = 3) :
    ∃ χ : DirichletCharacter ℂ d, IsKroneckerChar χ := by sorry
