-- Prove2me | Theorems.Thm_GeneralPieces_Dual_prod_map_sum
-- name    : GeneralPieces.Dual.prod_map_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:34:49.720029+00:00
-- url     : https://prove2.me/theorems/f12675c5-2cab-413d-a3f1-4c5cf56f5e05
-- title:
--   Dual: prod map sum
-- statement:
--   Multiplying out a product of sums.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L97-L103
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L97-L103

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces

theorem GeneralPieces.Dual.prod_map_sum {ι α R : Type} [DecidableEq α] [CommSemiring R] (L : List ι) (S : ι → Finset α) (f : ι → α → R) :
    (L.map fun i => ∑ a ∈ S i, f i a).prod = ∑ x ∈ tuples (L.map S), (List.zipWith f L x).prod := by sorry
