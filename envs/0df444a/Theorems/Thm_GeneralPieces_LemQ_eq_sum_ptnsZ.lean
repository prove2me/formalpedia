-- Prove2me | Theorems.Thm_GeneralPieces_LemQ_eq_sum_ptnsZ
-- name    : GeneralPieces.LemQ.eq_sum_ptnsZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:31:07.07192+00:00
-- url     : https://prove2.me/theorems/e1918142-801b-4cca-be66-d950b589b459
-- title:
--   Lem Q: eq sum ptns Z
-- statement:
--   A polynomial of weight E is a combination of the t^μ with |μ| = E.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L76-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L76-L77

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

theorem GeneralPieces.LemQ.eq_sum_ptnsZ {E : ℤ} {f : V} (hf : f ∈ VE E) : f = ∑ μ ∈ ptnsZ E, coef μ f • tpow μ := by sorry
