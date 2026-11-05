-- Prove2me | Theorems.Thm_GeneralPieces_Series_sum_qP_of
-- name    : GeneralPieces.Series.sum_qP_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:19:39.834718+00:00
-- url     : https://prove2.me/theorems/e3662eed-0c6a-4657-a0dd-828e459d9503
-- title:
--   Series: sum q P of
-- statement:
--   Claim (c) for monomials, with the constant a[−h]b.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/LemmaQ.lean#L75-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/LemmaQ.lean#L75-L82

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

theorem GeneralPieces.Series.sum_qP_of (h : StExpansion) {a : List ℕ} (ha : Pos a) (hb : Pos b) (hab : a.sum ≤ b.sum) {π σ : Multiset ℕ} (hπ : 0 ∉ π) (hσ : 0 ∉ σ) :
    ∑ s ∈ Icc (-((σ.sum : ℤ) + b.sum)) ((σ.sum : ℤ) + b.sum), qP a b s π σ = if π = σ then op a (-(b.sum : ℤ)) 0 (b : Multiset ℕ) else 0 := by sorry
