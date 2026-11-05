-- Prove2me | Theorems.Thm_GeneralPieces_GenF_coeff_emb
-- name    : GeneralPieces.GenF.coeff_emb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:30:35.277042+00:00
-- url     : https://prove2.me/theorems/b9287073-af44-4b5a-bfed-22fa55487e91
-- title:
--   Gen F: coeff emb
-- statement:
--   The Gen F construction uses the coeff emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L107-L107
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L107-L107

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

theorem GeneralPieces.GenF.coeff_emb (s : S) (y : ℤ) : (emb s).coeff y = MvPolynomial.C (s.coeff y) := by sorry
