-- Prove2me | Theorems.Thm_GeneralPieces_Series_ev_terms
-- name    : GeneralPieces.Series.ev_terms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:17:17.086301+00:00
-- url     : https://prove2.me/theorems/79153138-8a49-4b23-bff0-5dafa9938474
-- title:
--   Series: ev terms
-- statement:
--   At ω₁ = ω₂ = 1 only the terms with N_c = H remain.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/OneLaurent.lean#L63-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/OneLaurent.lean#L63-L73

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

theorem GeneralPieces.Series.ev_terms (H : ℕ) (v : L) (l : List (ℚ × ℕ × L)) (hl : ∀ c ∈ l, c.2.1 ≤ H) (ht : ∀ c ∈ l, c.2.1 = H → c.2.2 = v) :
    ev (l.map fun c => c.1 • (dW ^ (H - c.2.1) * c.2.2)).sum = ((l.filter fun c => c.2.1 = H).map fun c => c.1).sum * ev v := by sorry
