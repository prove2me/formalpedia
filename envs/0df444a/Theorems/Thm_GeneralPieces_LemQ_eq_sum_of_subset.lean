-- Prove2me | Theorems.Thm_GeneralPieces_LemQ_eq_sum_of_subset
-- name    : GeneralPieces.LemQ.eq_sum_of_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:30:59.594035+00:00
-- url     : https://prove2.me/theorems/18923249-97c0-460c-b3de-798c490db929
-- title:
--   Lem Q: eq sum of subset
-- statement:
--   A polynomial is the sum of its monomials, over any finite set of partitions that contains all
--   that occur.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L65-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L65-L73

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring

theorem GeneralPieces.LemQ.eq_sum_of_subset (f : V) (S : Finset Ptn) (hS : ∀ μ, coef μ f ≠ 0 → μ ∈ S) : f = ∑ μ ∈ S, coef μ f • tpow μ := by sorry
