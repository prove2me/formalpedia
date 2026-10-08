-- Prove2me | Theorems.Thm_MazurTransfer_order27_zero_columns_0_5
-- name    : MazurTransfer.order27_zero_columns_0_5
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T17:23:50.758167+00:00
-- url     : https://prove2.me/theorems/c72048f6-c2e4-4e96-b5a7-592e364d4a7c
-- title:
--   Order-27 zero certificate: columns 0 5
-- statement:
--   Let $C(f,\xi,b)$ denote the fixed sum of the seventeen original row entries in column $b$. For every $f,\xi\in\mathbb Q$,
--   \[C(f,\xi,b)=0\quad\text{for }b=0,\ldots,5.\]
--   These are the exact original band identities. Together with the remaining columns and the row reordering theorem, they imply the complete original numerator-zero identity.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Exact source data are exposed separately. Proof commands selected by kernel dependencies and resolved whole Lean AST ranges, with original Apache-2.0 headers. All rational parameters are universally quantified.

import Definitions.Def_MazurTransfer_Order27ZeroRowData

open MazurTorsion.Kubert

theorem MazurTransfer.order27_zero_columns_0_5 :
∀ f ξ : ℚ,
tlColumn f ξ (0 : Fin 24) = 0 ∧
tlColumn f ξ (1 : Fin 24) = 0 ∧
tlColumn f ξ (2 : Fin 24) = 0 ∧
tlColumn f ξ (3 : Fin 24) = 0 ∧
tlColumn f ξ (4 : Fin 24) = 0 ∧
tlColumn f ξ (5 : Fin 24) = 0 := by sorry
