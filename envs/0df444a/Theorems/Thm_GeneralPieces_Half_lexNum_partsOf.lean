-- Prove2me | Theorems.Thm_GeneralPieces_Half_lexNum_partsOf
-- name    : GeneralPieces.Half.lexNum_partsOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:37:45.988822+00:00
-- url     : https://prove2.me/theorems/5730dd0c-2244-4555-b3b0-60f8aee9f7f1
-- title:
--   Half: lex Num parts Of
-- statement:
--   The entry number k of the list of the partitions of h has the number k in the lexicographic
--   list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Order.lean#L76-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Order.lean#L76-L109

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Half_List
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Definitions.Def_GeneralPieces_Half_Order
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Half
open AppHalfPieces Finset ClauseBound.Part GeneralPieces.Ring Groundwork ClauseBound.Alg ClauseBound.Inst.Half

theorem GeneralPieces.Half.lexNum_partsOf (h k : ℕ) (hk : k < (partsOf h).length) : lexNum h (ptn (partsOf h)[k]) = k := by sorry
