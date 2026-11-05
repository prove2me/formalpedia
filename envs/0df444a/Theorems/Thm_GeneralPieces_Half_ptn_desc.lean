-- Prove2me | Theorems.Thm_GeneralPieces_Half_ptn_desc
-- name    : GeneralPieces.Half.ptn_desc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:38:22.853708+00:00
-- url     : https://prove2.me/theorems/c92589b7-232a-4bad-befa-3bb51e92ce1d
-- title:
--   Half: ptn desc
-- statement:
--   A partition is the partition of its nonincreasing sequence.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Order.lean#L68-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Order.lean#L68-L68

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Half_List
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Definitions.Def_GeneralPieces_Half_Order
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Half
open AppHalfPieces Finset ClauseBound.Part GeneralPieces.Ring Groundwork ClauseBound.Alg ClauseBound.Inst.Half

theorem GeneralPieces.Half.ptn_desc (ν : Ptn) : ptn (desc ν) = ν := by sorry
