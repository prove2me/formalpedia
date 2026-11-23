-- Prove2me | Theorems.Thm_GlobalTheory_IsKroneckerChar_ne_one
-- name    : GlobalTheory.IsKroneckerChar.ne_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:46.285797+00:00
-- url     : https://prove2.me/theorems/5030d39d-c579-4b31-9b58-68842b5f3ba2
-- title:
--   Is Kronecker Char: ne one
-- statement:
--   The Is Kronecker Char construction uses the ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L431-L434
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L431-L434

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

theorem GlobalTheory.IsKroneckerChar.ne_one (hd : 0 < d) : χ ≠ 1 := by sorry
