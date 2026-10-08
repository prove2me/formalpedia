-- Prove2me | Theorems.Thm_MazurTransfer_order27_zero_columns_6_7
-- name    : MazurTransfer.order27_zero_columns_6_7
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T17:54:38.34407+00:00
-- url     : https://prove2.me/theorems/1214835c-5711-4db4-8c13-3cfafbf93e25
-- title:
--   Order-27 zero certificate: columns 6 and 7
-- statement:
--   Let $C(f,\xi,b)$ be the fixed sum of the seventeen original row entries in column $b$. For every $f,\xi\in\mathbb Q$,
--   \[C(f,\xi,6)=0,\qquad C(f,\xi,7)=0.\]
--   These are exactly the indicated two original band identities. The complete numerator-zero certificate still requires all twenty-four columns; this pair supplies only its named indices.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Exact source data are exposed separately. Proof commands selected by kernel dependencies and resolved whole Lean AST ranges, with original Apache-2.0 headers. All rational parameters are universally quantified.

import Definitions.Def_MazurTransfer_Order27ZeroRowData

open MazurTorsion.Kubert

theorem MazurTransfer.order27_zero_columns_6_7 :
∀ f ξ : ℚ,
  tlColumn f ξ (6 : Fin 24) = 0 ∧
  tlColumn f ξ (7 : Fin 24) = 0 := by sorry
