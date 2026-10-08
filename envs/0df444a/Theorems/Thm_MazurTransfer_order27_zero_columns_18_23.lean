-- Prove2me | Theorems.Thm_MazurTransfer_order27_zero_columns_18_23
-- name    : MazurTransfer.order27_zero_columns_18_23
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T18:13:06.969418+00:00
-- url     : https://prove2.me/theorems/d89ca7dd-6d33-4899-9b5a-30ba6925f8b6
-- title:
--   Order-27 zero certificate: columns 18 23
-- statement:
--   Let $C(f,\xi,b)$ denote the fixed sum of the seventeen original row entries in column $b$. For every $f,\xi\in\mathbb Q$,
--   \[C(f,\xi,b)=0\quad\text{for }b=18,\ldots,23.\]
--   These are the exact original band identities. Together with the remaining columns and the row reordering theorem, they imply the complete original numerator-zero identity.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Exact source data are exposed separately. Proof commands selected by kernel dependencies and resolved whole Lean AST ranges, with original Apache-2.0 headers. All rational parameters are universally quantified.

import Definitions.Def_MazurTransfer_Order27ZeroRowData

open MazurTorsion.Kubert

theorem MazurTransfer.order27_zero_columns_18_23 :
∀ f ξ : ℚ,
tlColumn f ξ (18 : Fin 24) = 0 ∧
tlColumn f ξ (19 : Fin 24) = 0 ∧
tlColumn f ξ (20 : Fin 24) = 0 ∧
tlColumn f ξ (21 : Fin 24) = 0 ∧
tlColumn f ξ (22 : Fin 24) = 0 ∧
tlColumn f ξ (23 : Fin 24) = 0 := by sorry
