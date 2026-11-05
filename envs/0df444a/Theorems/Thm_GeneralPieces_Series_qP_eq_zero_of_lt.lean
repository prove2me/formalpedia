-- Prove2me | Theorems.Thm_GeneralPieces_Series_qP_eq_zero_of_lt
-- name    : GeneralPieces.Series.qP_eq_zero_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:18:17.72292+00:00
-- url     : https://prove2.me/theorems/5354d1ad-6c55-49f7-8b71-22e1753a460f
-- title:
--   Series: q P eq zero of lt
-- statement:
--   For s > E + h all terms of the first sum vanish.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/ReadOff.lean#L96-L97
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/ReadOff.lean#L96-L97

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

theorem GeneralPieces.Series.qP_eq_zero_of_lt (a b : List ℕ) (π : Multiset ℕ) {σ : Multiset ℕ} {s : ℤ} (h : (σ.sum : ℤ) + b.sum < s) : qP a b s π σ = 0 := by sorry
