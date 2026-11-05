-- Prove2me | Theorems.Thm_GeneralPieces_GenF_coeff_single_X
-- name    : GeneralPieces.GenF.coeff_single_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:30:40.370313+00:00
-- url     : https://prove2.me/theorems/c3b489de-0341-479d-a139-6f4935b1bce2
-- title:
--   Gen F: coeff single X
-- statement:
--   The Gen F construction uses the coeff single X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L220-L225
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L220-L225

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

theorem GeneralPieces.GenF.coeff_single_X (l k : ℕ) : MvPolynomial.coeff (Finsupp.single l 1) (MvPolynomial.X k : Vu) = if l = k then 1 else 0 := by sorry
