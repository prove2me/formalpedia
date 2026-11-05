-- Prove2me | Theorems.Thm_GeneralPieces_Series_Expansion_sum_qP
-- name    : GeneralPieces.Series.Expansion.sum_qP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:18:50.410439+00:00
-- url     : https://prove2.me/theorems/ada933e2-b813-4cf8-9a06-bca4c0ce4a8b
-- title:
--   Expansion: sum q P
-- statement:
--   Claim (c) for monomials, with the constant of the expansion: Σ_s ⟨Q_s(a,b)⟩ = F(1,1) = G·[π =
--   σ].
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/ReadOff.lean#L131-L134
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/ReadOff.lean#L131-L134

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_OneLaurent
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_GeneralPieces_Series_ReadOff
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset
variable {a b : List ℕ} {G : ℚ} {π σ : Multiset ℕ}

theorem GeneralPieces.Series.Expansion.sum_qP (X : Expansion a b G π σ) (hab : a.sum ≤ b.sum) :
    ∑ s ∈ Icc (-((σ.sum : ℤ) + b.sum)) ((σ.sum : ℤ) + b.sum), (qP a b s π σ : ℚ) = if π = σ then G else 0 := by sorry
