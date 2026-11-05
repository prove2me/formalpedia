-- Prove2me | Theorems.Thm_GeneralPieces_Consts_pad_le
-- name    : GeneralPieces.Consts.pad_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:38:51.965375+00:00
-- url     : https://prove2.me/theorems/0869c97f-ee82-41fe-b1d7-d3e7361af390
-- title:
--   Consts: pad le
-- statement:
--   The pad of the programs: if h ≤ c₀·λ² and Δ ≤ 2^{c₂λ}, then 2^10·(h+2)^4·(Δ+1)² ≤
--   2^{(4c₀+2c₂+28)λ}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Consts.lean#L78-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Consts.lean#L78-L96

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

theorem GeneralPieces.Consts.pad_le {c₀ c₂ lam h D : ℕ} (hl : 1 ≤ lam) (hh : h ≤ c₀ * lam ^ 2) (hD : D ≤ 2 ^ (c₂ * lam)) :
    2 ^ 10 * (h + 2) ^ 4 * (D + 1) ^ 2 ≤ 2 ^ ((4 * c₀ + 2 * c₂ + 28) * lam) := by sorry
