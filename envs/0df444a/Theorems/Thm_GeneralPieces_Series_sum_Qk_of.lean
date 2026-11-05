-- Prove2me | Theorems.Thm_GeneralPieces_Series_sum_Qk_of
-- name    : GeneralPieces.Series.sum_Qk_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:20:03.233231+00:00
-- url     : https://prove2.me/theorems/90daed05-c069-4b58-90bd-cfaa9db57be5
-- title:
--   Series: sum Qk of
-- statement:
--   Claim (c): on the monomials of weight E, the Q_s(a,b) with |s| ≤ E + h add up to (a[−h]b)·Id.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/LemmaQ.lean#L105-L115
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/LemmaQ.lean#L105-L115

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Constant
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_GeneralPieces_Series_LemmaQ
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset
variable {A : FA} {b : List ℕ}

theorem GeneralPieces.Series.sum_Qk_of (h : StExpansion) (hA : A.Ok b.sum) (hb : Pos b) {π σ : Multiset ℕ} (hπ : 0 ∉ π) (hσ : 0 ∉ σ) :
    ∑ s ∈ Icc (-((σ.sum : ℤ) + b.sum)) ((σ.sum : ℤ) + b.sum), Qk A b s π σ = if π = σ then pairF A b else 0 := by sorry
