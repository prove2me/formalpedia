-- Prove2me | Theorems.Thm_GeneralPieces_Series_Expansion_ev_F
-- name    : GeneralPieces.Series.Expansion.ev_F
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:17:30.35777+00:00
-- url     : https://prove2.me/theorems/fdd6730c-f256-491e-979e-328cf3715763
-- title:
--   Expansion: ev F
-- statement:
--   F(1,1) = G·[π = σ].
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/OneLaurent.lean#L76-L78
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/OneLaurent.lean#L76-L78

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Expansion
import Definitions.Def_GeneralPieces_Series_OneLaurent
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson
variable {a b : List ℕ} {G : ℚ} {π σ : Multiset ℕ}

theorem GeneralPieces.Series.Expansion.ev_F (X : Expansion a b G π σ) : ev X.F = if π = σ then G else 0 := by sorry
