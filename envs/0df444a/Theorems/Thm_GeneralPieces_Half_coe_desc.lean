-- Prove2me | Theorems.Thm_GeneralPieces_Half_coe_desc
-- name    : GeneralPieces.Half.coe_desc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:51:31.320195+00:00
-- url     : https://prove2.me/theorems/a2d73e68-c4e0-40df-8a67-3049f82bc928
-- title:
--   Half: coe desc
-- statement:
--   The Half construction uses the coe desc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Order.lean#L61-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Order.lean#L61-L61

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

theorem GeneralPieces.Half.coe_desc (ν : Ptn) : ((desc ν : List ℕ) : Multiset ℕ) = toN ν := by sorry
