-- Prove2me | Theorems.Thm_GeneralPieces_Series_Expansion_coeff_F_M
-- name    : GeneralPieces.Series.Expansion.coeff_F_M
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:17:35.207289+00:00
-- url     : https://prove2.me/theorems/c58e8574-1c28-438b-a272-e1b9a1d3d8d1
-- title:
--   Expansion: coeff F M
-- statement:
--   F_s is also the sum with the factors exchanged, from (ω₁ − ω₂)^H·f₋ = F.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/ReadOff.lean#L76-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/ReadOff.lean#L76-L82

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

theorem GeneralPieces.Series.Expansion.coeff_F_M (X : Expansion a b G π σ) (s : ℤ) : X.F.coeff (s, -s) = qM a b s π σ := by sorry
