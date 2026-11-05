-- Prove2me | Theorems.Thm_GeneralPieces_ThmHalfPieces_abs_fb_le
-- name    : GeneralPieces.ThmHalfPieces.abs_fb_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:26:57.93045+00:00
-- url     : https://prove2.me/theorems/16cd4b82-7c32-4192-a0e6-c602d385d33b
-- title:
--   Thm Half Pieces: abs fb le
-- statement:
--   The second factor is small at listed partitions.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L84-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L84-L96

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bits
import Definitions.Def_ClauseBound_Boson_Final
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.ThmHalfPieces
open AppHalfPieces Finset GeneralPieces.Ring GeneralPieces.Sizes GeneralPieces.Lex

theorem GeneralPieces.ThmHalfPieces.abs_fb_le (hP : PieceFacts) {h : ℕ} (hh : 1 ≤ h) {ν : Ptn} (hν : wt ν = h) (r : ℤ) {σ' σ : Ptn} (h1 : wt σ' ≤ 4 * h) (h2 : wt σ ≤ 4 * h) :
    |fb r ν σ' σ| ≤ 2 ^ ClauseBound.Boson.Half.eR h := by sorry
