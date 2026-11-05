-- Prove2me | Theorems.Thm_GeneralPieces_Series_pow_mul_terms
-- name    : GeneralPieces.Series.pow_mul_terms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:06:38.180014+00:00
-- url     : https://prove2.me/theorems/6d9e84cd-6b4a-4d48-9ad7-0b7a4b7eb1ae
-- title:
--   Series: pow mul terms
-- statement:
--   The same for a sum of terms and a homomorphism φ from 𝓛.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/OneLaurent.lean#L35-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/OneLaurent.lean#L35-L41

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

theorem GeneralPieces.Series.pow_mul_terms (φ : L →ₐ[ℚ] S) {e : S} (h : φ dW * e = 1) (H : ℕ) (l : List (ℚ × ℕ × L)) (hl : ∀ c ∈ l, c.2.1 ≤ H) :
    φ dW ^ H * (l.map fun c => c.1 • (e ^ c.2.1 * φ c.2.2)).sum = φ (l.map fun c => c.1 • (dW ^ (H - c.2.1) * c.2.2)).sum := by sorry
