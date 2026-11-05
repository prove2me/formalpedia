-- Prove2me | Theorems.Thm_GeneralPieces_Consts_four_mul_rho_le
-- name    : GeneralPieces.Consts.four_mul_rho_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:39:23.577588+00:00
-- url     : https://prove2.me/theorems/6c29bf47-bbde-4a9d-a6ae-4f52cfacf019
-- title:
--   Consts: four mul rho le
-- statement:
--   4ρ = 2√2 ≤ 3.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Consts.lean#L61-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Consts.lean#L61-L64

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_GeneralPieces_Half_Consts
set_option autoImplicit false
section
section
open GeneralPieces
open Finset Real ClauseBound.Inst.Half
open GeneralPieces.Consts

theorem GeneralPieces.Consts.four_mul_rho_le : 4 * (1 / √(2 : ℝ)) ≤ 3 := by sorry
