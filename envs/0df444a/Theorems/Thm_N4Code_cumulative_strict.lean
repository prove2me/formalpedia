-- Prove2me | Theorems.Thm_N4Code_cumulative_strict
-- name    : N4Code.cumulative_strict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:08:08.424438+00:00
-- url     : https://prove2.me/theorems/5b808cd5-10c5-4abe-b708-c12202dae018
-- title:
--   N4 Code: cumulative strict
-- statement:
--   Corollary `cor:1` (Corollary 21) (2): all Ψ_d ≥ 0 and some Ψ_d > 0 ⇒ λ_{C'} > λ_C.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L1348-L1434
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L1348-L1434

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.cumulative_strict {n : ℕ} (C C' : Code n) (t : Fin n)
    (hcol : C t = col1) (hcol' : C' t = col3)
    (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    (hge : ∀ d ∈ Finset.Icc 1 n, Psi C t d ≥ 0)
    (hgt : ∃ d ∈ Finset.Icc 1 n, Psi C t d > 0) :
    UniversalStrictBetter C' C := by sorry
