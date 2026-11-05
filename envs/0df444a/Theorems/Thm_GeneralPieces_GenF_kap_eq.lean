-- Prove2me | Theorems.Thm_GeneralPieces_GenF_kap_eq
-- name    : GeneralPieces.GenF.kap_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:33:15.810055+00:00
-- url     : https://prove2.me/theorems/6809b74b-0df7-41eb-877e-85d6e34fd225
-- title:
--   Gen F: kap eq
-- statement:
--   The Gen F construction uses the kap eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Commute.lean#L79-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Commute.lean#L79-L79

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_Commute
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
open MvPowerSeries hiding C X

theorem GeneralPieces.GenF.kap_eq (rd : Bool) : kap rd = bil (kq rd) := by sorry
