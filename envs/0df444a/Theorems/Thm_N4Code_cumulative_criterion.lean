-- Prove2me | Theorems.Thm_N4Code_cumulative_criterion
-- name    : N4Code.cumulative_criterion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:07:42.985181+00:00
-- url     : https://prove2.me/theorems/80e556cd-a91a-4bfc-a38f-7a90d89ad55a
-- title:
--   N4 Code: cumulative criterion
-- statement:
--   Corollary `cor:1` (Corollary 21) (1): all Ψ_d = 0 ⇒ λ_{C'} = λ_C.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L1314-L1345
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L1314-L1345

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.cumulative_criterion {n : ℕ} (C C' : Code n) (t : Fin n)
    (hcol : C t = col1) (hcol' : C' t = col3)
    (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    (hΨ : ∀ d ∈ Finset.Icc 1 n, Psi C t d = 0) : UniversalEqual C' C := by sorry
