-- Prove2me | Theorems.Thm_GeneralPieces_Series_Expansion_qP_eq_zero
-- name    : GeneralPieces.Series.Expansion.qP_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:07:16.198475+00:00
-- url     : https://prove2.me/theorems/420b37d7-8170-4e28-8a49-aff444c2b107
-- title:
--   Expansion: q P eq zero
-- statement:
--   Claim (b) for monomials: Q_s(a,b) = 0 for |s| > E + h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/ReadOff.lean#L106-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/ReadOff.lean#L106-L109

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

theorem GeneralPieces.Series.Expansion.qP_eq_zero (X : Expansion a b G π σ) (hab : a.sum ≤ b.sum) {s : ℤ} (hs : (σ.sum : ℤ) + b.sum < |s|) : qP a b s π σ = 0 := by sorry
