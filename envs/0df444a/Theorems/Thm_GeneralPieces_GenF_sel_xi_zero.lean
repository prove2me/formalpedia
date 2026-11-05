-- Prove2me | Theorems.Thm_GeneralPieces_GenF_sel_xi_zero
-- name    : GeneralPieces.GenF.sel_xi_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:32:03.103213+00:00
-- url     : https://prove2.me/theorems/73783e98-e2cf-480f-a900-1fbf9d23e81b
-- title:
--   Gen F: sel xi zero
-- statement:
--   The Gen F construction uses the sel xi zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L43-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L43-L44

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
variable {R : Type} [Zero R]

theorem GeneralPieces.GenF.sel_xi_zero (rd : Bool) (f g : ℕ → R) : sel rd f g (xi rd 0) = 0 := by sorry
