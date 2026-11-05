-- Prove2me | Theorems.Thm_GeneralPieces_Series_qM_eq_zero_of_lt
-- name    : GeneralPieces.Series.qM_eq_zero_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:18:37.618291+00:00
-- url     : https://prove2.me/theorems/710e6321-99a5-4d87-884a-e6398111fce9
-- title:
--   Series: q M eq zero of lt
-- statement:
--   For s < −E − h all terms of the second sum vanish; here h' ≤ h is used.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/ReadOff.lean#L100-L103
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/ReadOff.lean#L100-L103

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

theorem GeneralPieces.Series.qM_eq_zero_of_lt {a b : List ℕ} (hab : a.sum ≤ b.sum) (π : Multiset ℕ) {σ : Multiset ℕ} {s : ℤ} (h : s < -(σ.sum : ℤ) - b.sum) : qM a b s π σ = 0 := by sorry
