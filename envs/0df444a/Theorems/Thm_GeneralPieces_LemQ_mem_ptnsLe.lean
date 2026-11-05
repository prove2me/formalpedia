-- Prove2me | Theorems.Thm_GeneralPieces_LemQ_mem_ptnsLe
-- name    : GeneralPieces.LemQ.mem_ptnsLe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:31:10.73646+00:00
-- url     : https://prove2.me/theorems/5422f6d0-a484-46e0-82a2-cc82a1857162
-- title:
--   Lem Q: mem ptns Le
-- statement:
--   The Lem Q construction uses the mem ptns Le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L89-L92
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L89-L92

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

theorem GeneralPieces.LemQ.mem_ptnsLe (h : ℕ) (μ : Ptn) : μ ∈ ptnsLe h ↔ wt μ ≤ h := by sorry
