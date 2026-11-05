-- Prove2me | Theorems.Thm_GeneralPieces_Dual_tpow_cons
-- name    : GeneralPieces.Dual.tpow_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:35:08.2974+00:00
-- url     : https://prove2.me/theorems/051fa7bf-9120-4441-926d-83e33dfec09f
-- title:
--   Dual: tpow cons
-- statement:
--   t^μ for a list with a first part.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L160-L162
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L160-L162

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces

theorem GeneralPieces.Dual.tpow_cons (a : ℕ+) (l : List ℕ+) : tpow ((a :: l : List ℕ+) : Multiset ℕ+) = X a * tpow (l : Multiset ℕ+) := by sorry
