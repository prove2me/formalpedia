-- Prove2me | Theorems.Thm_GeneralPieces_exists_cst2
-- name    : GeneralPieces.exists_cst2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:39:02.260413+00:00
-- url     : https://prove2.me/theorems/fdeaa0bd-9be1-417a-8bf9-5dfd66931175
-- title:
--   General Pieces: exists cst2
-- statement:
--   The choice of the constants in the last sentence of the proof, «if c is large enough»: there are
--   constants c₀ and c that are large enough for the programs at every length.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Consts.lean#L104-L127
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Consts.lean#L104-L127

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
open Consts

theorem GeneralPieces.exists_cst2 (hT : AppHalfPieces.ThmHalfPiecesPure) : ∃ c₀ c : ℕ, ∀ lam : ℕ, 1 ≤ lam → Cst c₀ c lam := by sorry
