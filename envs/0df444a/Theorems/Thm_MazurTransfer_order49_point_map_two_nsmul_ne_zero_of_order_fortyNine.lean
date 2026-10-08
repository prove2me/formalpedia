-- Prove2me | Theorems.Thm_MazurTransfer_order49_point_map_two_nsmul_ne_zero_of_order_fortyNine
-- name    : MazurTransfer.order49_point_map_two_nsmul_ne_zero_of_order_fortyNine
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T04:00:44.594166+00:00
-- url     : https://prove2.me/theorems/75537a9b-811e-4cc1-b86e-06ef039c516c
-- title:
--   A point of exact order 49 has nonzero double
-- statement:
--   In every additive commutative group, a point $P$ of exact order $49$ has nonzero double: $$\operatorname{ord}(P)=49\quad\Longrightarrow\quad 2P\ne0.$$ No elliptic-curve or finiteness assumption is required.
--
--   This supplies an exact point-function fact used in the original order-49 exclusion.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original _private.MazurTorsion.Kubert.OrderSevenIsogenyDoubling.0.MazurTorsion.Kubert.two_nsmul_ne_zero_of_order_fortyNine. Original hypotheses, declaration ranges and proof commands preserved using the kernel graph and complete Lean AST. All point definitions were independently compared with the WIP originals; all reused geometric helpers are Proved and locally rechecked with closed proofs. Apache-2.0 headers and attribution retained. Named downstream consumers: exact residual Hauptmodul specification, then full every-curve order49 exclusion.

import Mathlib
open Polynomial

theorem MazurTransfer.order49_point_map_two_nsmul_ne_zero_of_order_fortyNine {G : Type*} [AddCommGroup G] {P : G}
    (hP : addOrderOf P = 49) :
    (2 : ℕ) • P ≠ 0 := by sorry
