-- Prove2me | Theorems.Thm_GeneralPieces_Half_val_eq
-- name    : GeneralPieces.Half.val_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:39:36.332014+00:00
-- url     : https://prove2.me/theorems/6b5cd0cc-48b1-4cf2-a22c-3d700b686313
-- title:
--   Half: val eq
-- statement:
--   A string read as an integer, first bit lowest, is the number that the programs read.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Order.lean#L112-L122
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Order.lean#L112-L122

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

theorem GeneralPieces.Half.val_eq {lam : ℕ} (x : Pieces.Bits lam) : AppHalfPieces.val x = ofWord (bitsOf x) := by sorry
