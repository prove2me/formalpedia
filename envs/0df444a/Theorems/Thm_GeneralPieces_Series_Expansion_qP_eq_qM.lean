-- Prove2me | Theorems.Thm_GeneralPieces_Series_Expansion_qP_eq_qM
-- name    : GeneralPieces.Series.Expansion.qP_eq_qM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:07:11.263608+00:00
-- url     : https://prove2.me/theorems/0f3cbed6-bf74-4829-8a6a-367e9bdb78e8
-- title:
--   Expansion: q P eq q M
-- statement:
--   Claim (a) for monomials: Q_s(a,b) does not change if the two factors are exchanged in all
--   products at once.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/ReadOff.lean#L92-L93
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/ReadOff.lean#L92-L93

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

theorem GeneralPieces.Series.Expansion.qP_eq_qM (X : Expansion a b G π σ) (s : ℤ) : qP a b s π σ = qM a b s π σ := by sorry
