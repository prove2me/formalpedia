-- Prove2me | Theorems.Thm_GeneralPieces_LemQ_eq_sum_ptnsLe
-- name    : GeneralPieces.LemQ.eq_sum_ptnsLe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:20:31.436964+00:00
-- url     : https://prove2.me/theorems/3970e4f9-9bc1-415e-a29c-d7adb8d498fd
-- title:
--   Lem Q: eq sum ptns Le
-- statement:
--   a = Σ_{h' ≤ h} ā_{h'} is a combination of the t^μ with |μ| ≤ h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L95-L101
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L95-L101

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

theorem GeneralPieces.LemQ.eq_sum_ptnsLe {h : ℕ} {a : V} (ha : WtLe h a) : a = ∑ μ ∈ ptnsLe h, coef μ a • tpow μ := by sorry
