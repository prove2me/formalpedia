-- Prove2me | Theorems.Thm_GeneralPieces_Half_sum_Icc_eq_list
-- name    : GeneralPieces.Half.sum_Icc_eq_list
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:39:26.144629+00:00
-- url     : https://prove2.me/theorems/fe2c1dd1-4fd8-40e9-90a2-e6ed60393c71
-- title:
--   Half: sum Icc eq list
-- statement:
--   A sum over 1, …, n as the sum of a list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L122-L125
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L122-L125

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_HalfList
import Definitions.Def_GeneralPieces_Half_List
set_option autoImplicit false
section
section
open GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
open GeneralPieces.Half

theorem GeneralPieces.Half.sum_Icc_eq_list (f : ℕ → V) (n : ℕ) : ∑ j ∈ Icc 1 n, f j = ((List.range n).map fun i => f (i + 1)).sum := by sorry
