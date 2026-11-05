-- Prove2me | Theorems.Thm_GeneralPieces_Series_Expansion_coeff_F_P
-- name    : GeneralPieces.Series.Expansion.coeff_F_P
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:06:53.276308+00:00
-- url     : https://prove2.me/theorems/776b9c89-0eac-4fbd-acaf-99c41e4e29f4
-- title:
--   Expansion: coeff F P
-- statement:
--   F_s = ⟨Q_s(a,b)⟩, from (ω₁ − ω₂)^H·f₊ = F.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/ReadOff.lean#L67-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/ReadOff.lean#L67-L73

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

theorem GeneralPieces.Series.Expansion.coeff_F_P (X : Expansion a b G π σ) (s : ℤ) : X.F.coeff (s, -s) = qP a b s π σ := by sorry
