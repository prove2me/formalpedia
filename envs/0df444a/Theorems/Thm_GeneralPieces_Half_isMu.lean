-- Prove2me | Theorems.Thm_GeneralPieces_Half_isMu
-- name    : GeneralPieces.Half.isMu
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:52:07.868503+00:00
-- url     : https://prove2.me/theorems/4b5cfa05-8b87-428d-bd75-b10a68ea8d86
-- title:
--   Half: is Mu
-- statement:
--   The partition that the programs read from the string x is the partition of h with number x in
--   the lexicographic list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Order.lean#L126-L137
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Order.lean#L126-L137

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

theorem GeneralPieces.Half.isMu {lam h : ℕ} (hp : 2 ^ lam ≤ Partitions.p h) : IsMu lam h fun x => ptn (ell h x) := by sorry
