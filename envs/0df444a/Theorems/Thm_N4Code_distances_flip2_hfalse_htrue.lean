-- Prove2me | Theorems.Thm_N4Code_distances_flip2_hfalse_htrue
-- name    : N4Code.distances_flip2_hfalse_htrue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:20:31.632347+00:00
-- url     : https://prove2.me/theorems/bb2d2888-a5e3-47e9-83d9-88b166ecd1d2
-- title:
--   N4 Code: distances flip2 hfalse htrue
-- statement:
--   Distance values at F₂ y in terms of their values at y, (f,t) orientation.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L556-L572
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L556-L572

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.distances_flip2_hfalse_htrue {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (y : Word n)
    (hy1 : y t₁ = false) (hy2 : y t₂ = true) :
    dO C (flipTwoBits t₁ t₂ y) = dOp2 C t₁ t₂ y ∧
      dP C (flipTwoBits t₁ t₂ y) = dP C y + 2 ∧
      dOp2 C t₁ t₂ (flipTwoBits t₁ t₂ y) = dO C y ∧
      dPp2 C t₁ t₂ (flipTwoBits t₁ t₂ y) = dP C y := by sorry
