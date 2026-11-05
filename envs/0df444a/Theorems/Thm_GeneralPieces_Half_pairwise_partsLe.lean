-- Prove2me | Theorems.Thm_GeneralPieces_Half_pairwise_partsLe
-- name    : GeneralPieces.Half.pairwise_partsLe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:40:26.177011+00:00
-- url     : https://prove2.me/theorems/1f90301b-d467-4d8b-9a9d-e8181bf6cc1b
-- title:
--   Half: pairwise parts Le
-- statement:
--   The list of the partitions of E into parts of size at most k is strictly increasing in the
--   lexicographic order.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Order.lean#L31-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Order.lean#L31-L53

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

theorem GeneralPieces.Half.pairwise_partsLe (E k : ℕ) : (partsLe E k).Pairwise (· < ·) := by sorry
