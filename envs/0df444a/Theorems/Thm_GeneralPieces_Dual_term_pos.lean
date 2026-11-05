-- Prove2me | Theorems.Thm_GeneralPieces_Dual_term_pos
-- name    : GeneralPieces.Dual.term_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:35:01.726056+00:00
-- url     : https://prove2.me/theorems/3a3e0527-decf-48a2-8801-9347bb2e47d3
-- title:
--   Dual: term pos
-- statement:
--   A term of display (47) with all k_i positive: there are only differentiations.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L134-L140
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L134-L140

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

theorem GeneralPieces.Dual.term_pos (μ : List ℕ+) (ks : List ℤ) (f : V) (h : ∀ k ∈ ks, 1 ≤ k) :
    term μ ks f = (((List.zipWith (fun (m : ℕ+) (k : ℤ) => binom (-k - 1) ((m : ℤ) - 1)) μ ks).prod : ℤ) : ℚ) • nablas ks f := by sorry
