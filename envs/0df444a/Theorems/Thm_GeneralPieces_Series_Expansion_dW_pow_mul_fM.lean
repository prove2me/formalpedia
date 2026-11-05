-- Prove2me | Theorems.Thm_GeneralPieces_Series_Expansion_dW_pow_mul_fM
-- name    : GeneralPieces.Series.Expansion.dW_pow_mul_fM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:17:01.266878+00:00
-- url     : https://prove2.me/theorems/3de5e2fe-126a-4bec-afbc-b5f0edc0bd50
-- title:
--   Expansion: d W pow mul f M
-- statement:
--   (ω₁ − ω₂)^H·f₋ = F in 𝓛₋.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/OneLaurent.lean#L49-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/OneLaurent.lean#L49-L51

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

theorem GeneralPieces.Series.Expansion.dW_pow_mul_fM (X : Expansion a b G π σ) : toM dW ^ (a.sum + b.sum) * fM a b π σ = toM X.F := by sorry
