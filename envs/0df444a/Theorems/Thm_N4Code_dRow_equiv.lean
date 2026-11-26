-- Prove2me | Theorems.Thm_N4Code_dRow_equiv
-- name    : N4Code.dRow_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:59:15.386308+00:00
-- url     : https://prove2.me/theorems/974cc9f6-7c15-5009-a0e2-4c18cca699ec
-- title:
--   N4 Code: d Row equiv
-- statement:
--   Row distances transform along the equivalence.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L169-L193
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L169-L193

import Definitions.Def_N4Code_Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_Performance
set_option autoImplicit true
open scoped BigOperators
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.dRow_equiv {n : ℕ} (C C' : Code n) {ρ : Equiv (Fin 4) (Fin 4)}
    {p : Equiv (Fin n) (Fin n)} {f : Fin n → Bool}
    (h : ∀ t : Fin n, C' (p t) = rowPermute ρ (if f t then flipCol (C t) else C t))
    (j : Fin 4) (y : Word n) :
    dRow C' j y = dRow C (ρ j) (wordTransform p f y) := by sorry
