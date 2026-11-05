-- Prove2me | Theorems.Thm_GeneralPieces_Series_ev_dW
-- name    : GeneralPieces.Series.ev_dW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:17:14.192901+00:00
-- url     : https://prove2.me/theorems/f30bb341-266b-4dcf-977d-6cfab6636ae9
-- title:
--   Series: ev d W
-- statement:
--   The Series construction uses the ev d W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/OneLaurent.lean#L60-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/OneLaurent.lean#L60-L60

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

theorem GeneralPieces.Series.ev_dW : ev dW = 0 := by sorry
