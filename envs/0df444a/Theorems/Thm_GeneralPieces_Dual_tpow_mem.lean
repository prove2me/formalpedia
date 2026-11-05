-- Prove2me | Theorems.Thm_GeneralPieces_Dual_tpow_mem
-- name    : GeneralPieces.Dual.tpow_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:36:18.623839+00:00
-- url     : https://prove2.me/theorems/939e0c07-25d3-4cc6-a353-f30631d1c0cb
-- title:
--   Dual: tpow mem
-- statement:
--   t^ν ∈ V_{|ν|}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L472-L474
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L472-L474

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

theorem GeneralPieces.Dual.tpow_mem (ν : Ptn) : tpow ν ∈ VE (wt ν) := by sorry
