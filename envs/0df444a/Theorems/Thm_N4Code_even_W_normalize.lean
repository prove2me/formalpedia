-- Prove2me | Theorems.Thm_N4Code_even_W_normalize
-- name    : N4Code.even_W_normalize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:14:17.482246+00:00
-- url     : https://prove2.me/theorems/798befa0-802f-48d1-9d99-82a82c56fbc3
-- title:
--   N4 Code: even W normalize
-- statement:
--   The normalized code has even W = |4|+|5|+|6|+|7|.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2118-L2127
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2118-L2127

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.even_W_normalize {n : ℕ} (C : Code n) (i j : Fin 4) (hij : i ≠ j)
    (hEven : Even (hammingDist (row C i) (row C j))) :
    Even (count (normalizeCode C i j) 4 + count (normalizeCode C i j) 5 +
      count (normalizeCode C i j) 6 + count (normalizeCode C i j) 7) := by sorry
