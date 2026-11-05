-- Prove2me | Theorems.Thm_GeneralPieces_Pcs_aFam_cons
-- name    : GeneralPieces.Pcs.aFam_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:36:43.237574+00:00
-- url     : https://prove2.me/theorems/d3abb3f9-610e-473e-8699-6b5c85d725e3
-- title:
--   Pcs: a Fam cons
-- statement:
--   The Pcs construction uses the a Fam cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Pieces.lean#L113-L115
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Pieces.lean#L113-L115

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ

theorem GeneralPieces.Pcs.aFam_cons (n : ℕ+) (μ : Ptn) : aFam (n ::ₘ μ) = ((-1 : ℚ) ^ ((n : ℕ) - 1) • y n) * aFam μ := by sorry
