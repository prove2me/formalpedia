-- Prove2me | Theorems.Thm_GeneralPieces_Ring_exists_window
-- name    : GeneralPieces.Ring.exists_window
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:26:35.59472+00:00
-- url     : https://prove2.me/theorems/cf85ba39-c3ee-4ca2-9329-1d53518612df
-- title:
--   Ring: exists window
-- statement:
--   A window that is large enough for f and r.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L122-L124
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L122-L124

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset

theorem GeneralPieces.Ring.exists_window (f : V) (r : ℤ) : ∃ (E : ℤ) (M : ℕ), Bd f E ∧ E ≤ M ∧ E + r ≤ M := by sorry
