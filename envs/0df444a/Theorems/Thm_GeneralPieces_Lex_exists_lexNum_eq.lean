-- Prove2me | Theorems.Thm_GeneralPieces_Lex_exists_lexNum_eq
-- name    : GeneralPieces.Lex.exists_lexNum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:23:04.385887+00:00
-- url     : https://prove2.me/theorems/38e3c20b-18d0-4d9d-b543-43aaae56781d
-- title:
--   Lex: exists lex Num eq
-- statement:
--   Every j < p(h) is the number of a partition of h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Lex.lean#L91-L92
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Lex.lean#L91-L92

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_Bridge
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Lex
import Definitions.Def_GeneralPieces_Ring_Lex
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Lex
open AppHalfPieces Finset

theorem GeneralPieces.Lex.exists_lexNum_eq {h j : ℕ} (hj : j < Partitions.p h) : ∃ μ ∈ ptns h, lexNum h μ = j := by sorry
