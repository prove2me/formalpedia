-- Prove2me | Theorems.Thm_GlobalTheory_isKroneckerChar_quadraticChar
-- name    : GlobalTheory.isKroneckerChar_quadraticChar
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:58:12.0768+00:00
-- url     : https://prove2.me/theorems/1b80d638-475d-4a0a-8678-42fcb77168f0
-- title:
--   Global Theory: is Kronecker Char quadratic Char
-- statement:
--   The Global Theory construction uses the is Kronecker Char quadratic Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L448-L451
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L448-L451

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

theorem GlobalTheory.isKroneckerChar_quadraticChar {d : ℕ} [Fact d.Prime] (hd : d % 4 = 3) :
    IsKroneckerChar ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)) := by sorry
