-- Prove2me | Theorems.Thm_GeneralPieces_Dual_weight_toFinsupp
-- name    : GeneralPieces.Dual.weight_toFinsupp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:36:16.280808+00:00
-- url     : https://prove2.me/theorems/fe070882-bba1-4f84-91a4-ae90f7f45dbd
-- title:
--   Dual: weight to Finsupp
-- statement:
--   The weight of the monomial t^ν is |ν|.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L464-L469
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L464-L469

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
import Theorems.Thm_GeneralPieces_Ring_weight_toFinsupp

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces

theorem GeneralPieces.Dual.weight_toFinsupp (ν : Ptn) : Finsupp.weight (fun k : ℕ+ => (k : ℕ)) (Multiset.toFinsupp ν) = wt ν := by sorry
