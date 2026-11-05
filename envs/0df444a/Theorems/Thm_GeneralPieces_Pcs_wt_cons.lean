-- Prove2me | Theorems.Thm_GeneralPieces_Pcs_wt_cons
-- name    : GeneralPieces.Pcs.wt_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:23:49.947714+00:00
-- url     : https://prove2.me/theorems/86832b8a-38b0-494f-af8a-1032af1d1a23
-- title:
--   Pcs: wt cons
-- statement:
--   The Pcs construction uses the wt cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Pieces.lean#L100-L100
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Pieces.lean#L100-L100

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces
import Theorems.Thm_ClauseBound_Boson_Text_wt_cons

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ

theorem GeneralPieces.Pcs.wt_cons (n : ℕ+) (μ : Ptn) : wt (n ::ₘ μ) = n + wt μ := by sorry
