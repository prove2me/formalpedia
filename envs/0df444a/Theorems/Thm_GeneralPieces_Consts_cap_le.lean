-- Prove2me | Theorems.Thm_GeneralPieces_Consts_cap_le
-- name    : GeneralPieces.Consts.cap_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:39:15.312803+00:00
-- url     : https://prove2.me/theorems/a0cbeacd-9cc6-4930-a0a6-739323fab01d
-- title:
--   Consts: cap le
-- statement:
--   Two numbers of bits with a + b ≤ 4ρλ + c·log 2λ have a + b ≤ (3 + c)·λ, because 4ρ ≤ 3 and log
--   2λ ≤ λ. So the cut-off of the programs at 2c'λ bits is not active if 3 + c ≤ 2c'.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Consts.lean#L68-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Consts.lean#L68-L74

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

theorem GeneralPieces.Consts.cap_le {a b c lam : ℕ} (hl : 1 ≤ lam) (h : ((a + b : ℕ) : ℝ) ≤ 4 * (1 / √2) * lam + c * logb 2 (2 * lam)) : a + b ≤ (3 + c) * lam := by sorry
