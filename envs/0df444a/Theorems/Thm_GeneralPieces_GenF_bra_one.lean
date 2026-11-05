-- Prove2me | Theorems.Thm_GeneralPieces_GenF_bra_one
-- name    : GeneralPieces.GenF.bra_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:05:50.873558+00:00
-- url     : https://prove2.me/theorems/9c749032-88f4-45a1-9431-603216244585
-- title:
--   Gen F: bra one
-- statement:
--   The Gen F construction uses the bra one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L158-L159
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L158-L159

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial

theorem GeneralPieces.GenF.bra_one (σ : Multiset ℕ) : bra σ 1 = if σ = 0 then 1 else 0 := by sorry
