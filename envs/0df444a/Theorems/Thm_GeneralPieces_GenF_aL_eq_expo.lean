-- Prove2me | Theorems.Thm_GeneralPieces_GenF_aL_eq_expo
-- name    : GeneralPieces.GenF.aL_eq_expo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:13:20.890771+00:00
-- url     : https://prove2.me/theorems/5f044e57-d28e-474e-8c8a-ebe20958e0b9
-- title:
--   Gen F: a L eq expo
-- statement:
--   The Gen F construction uses the a L eq expo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/YY.lean#L112-L114
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/YY.lean#L112-L114

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_GeneralPieces_GenF_YY
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial Finset

theorem GeneralPieces.GenF.aL_eq_expo (ι : ℕ → X) (a : List ℕ) : aL ι a = expo (a.map ι) := by sorry
