-- Prove2me | Theorems.Thm_GeneralPieces_Half_desc_mem_partsOf
-- name    : GeneralPieces.Half.desc_mem_partsOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:39:35.014253+00:00
-- url     : https://prove2.me/theorems/52d54511-425d-4d58-be7f-8649ef8c5505
-- title:
--   Half: desc mem parts Of
-- statement:
--   The nonincreasing sequence of a partition of h is in the list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Order.lean#L71-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Order.lean#L71-L72

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

theorem GeneralPieces.Half.desc_mem_partsOf {h : ℕ} {ν : Ptn} (hν : ν ∈ ptns h) : desc ν ∈ partsOf h := by sorry
