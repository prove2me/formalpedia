-- Prove2me | Theorems.Thm_GeneralPieces_Series_Qk_eq_zero_of
-- name    : GeneralPieces.Series.Qk_eq_zero_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:20:13.013665+00:00
-- url     : https://prove2.me/theorems/cf77736d-bf70-4278-8869-e42f234169ac
-- title:
--   Series: Qk eq zero of
-- statement:
--   Claim (b): Q_s(a,b) vanishes on the monomials of weight E for |s| > E + h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/LemmaQ.lean#L95-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/LemmaQ.lean#L95-L102

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

theorem GeneralPieces.Series.Qk_eq_zero_of (h : StExpansion) (hA : A.Ok b.sum) (hb : Pos b) {s : ℤ} {π σ : Multiset ℕ} (hπ : 0 ∉ π) (hσ : 0 ∉ σ) (hs : (σ.sum : ℤ) + b.sum < |s|) :
    Qk A b s π σ = 0 := by sorry
