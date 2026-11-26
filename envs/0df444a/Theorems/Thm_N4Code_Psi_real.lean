-- Prove2me | Theorems.Thm_N4Code_Psi_real
-- name    : N4Code.Psi_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:04:31.627853+00:00
-- url     : https://prove2.me/theorems/a1268a4c-b21a-5cbd-b000-eea45b8d2c2e
-- title:
--   N4 Code: Psi real
-- statement:
--   The real prefix sums of α³(i) − α⁵(i−1) equal the integer Ψ_d.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L1259-L1282
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L1259-L1282

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.Psi_real {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ) (hd : 1 ≤ d) :
    (∑ i ∈ Finset.Icc 1 d, ((alpha3 C t i : ℝ) - (alpha5 C t (i - 1) : ℝ))) =
      Psi C t d := by sorry
