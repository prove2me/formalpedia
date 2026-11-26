-- Prove2me | Theorems.Thm_N4Code_dRow_eq_mInd
-- name    : N4Code.dRow_eq_mInd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:17:47.695734+00:00
-- url     : https://prove2.me/theorems/f36d0828-deb6-4bee-b78f-61f4ae28569f
-- title:
--   N4 Code: d Row eq m Ind
-- statement:
--   d_j(w) is the sum of the mismatch indicators.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L146-L149
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L146-L149

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.dRow_eq_mInd {n : ℕ} (C : Code n) (j : Fin 4) (w : Word n) :
    dRow C j w = ∑ u : Fin n, mInd C j w u := by sorry
