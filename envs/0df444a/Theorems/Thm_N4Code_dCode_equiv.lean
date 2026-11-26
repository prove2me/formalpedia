-- Prove2me | Theorems.Thm_N4Code_dCode_equiv
-- name    : N4Code.dCode_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:58:50.660802+00:00
-- url     : https://prove2.me/theorems/5030c0c4-77da-589e-b61b-a39d14b4738c
-- title:
--   N4 Code: d Code equiv
-- statement:
--   The code distance transforms along the equivalence.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L196-L211
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L196-L211

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

theorem N4Code.dCode_equiv {n : ℕ} (C C' : Code n) {ρ : Equiv (Fin 4) (Fin 4)}
    {p : Equiv (Fin n) (Fin n)} {f : Fin n → Bool}
    (h : ∀ t : Fin n, C' (p t) = rowPermute ρ (if f t then flipCol (C t) else C t))
    (y : Word n) :
    dCode C' y = dCode C (wordTransform p f y) := by sorry
