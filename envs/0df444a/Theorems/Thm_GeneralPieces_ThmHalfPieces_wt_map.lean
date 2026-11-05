-- Prove2me | Theorems.Thm_GeneralPieces_ThmHalfPieces_wt_map
-- name    : GeneralPieces.ThmHalfPieces.wt_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:27:18.910103+00:00
-- url     : https://prove2.me/theorems/54063c64-7c3b-480b-8b22-551b6081e26e
-- title:
--   Thm Half Pieces: wt map
-- statement:
--   The weight of a monomial of the matrices, as a partition.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L174-L178
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean#L174-L178

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
variable {lam h : ℕ} {mu : Pieces.Bits lam → Ptn}

theorem GeneralPieces.ThmHalfPieces.wt_map {m : ℤ} {τ : Multiset ℕ} (hτ : τ ∈ ClauseBound.Boson.Pz m) : (wt (τ.map Nat.toPNat') : ℤ) = m := by sorry
