-- Prove2me | Theorems.Thm_GeneralPieces_GenF_DD_sel
-- name    : GeneralPieces.GenF.DD_sel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:33:27.022037+00:00
-- url     : https://prove2.me/theorems/3ec81632-619a-491a-9f44-c0971319e971
-- title:
--   Gen F: DD sel
-- statement:
--   The operator beside x_i in A⁻, applied to the coefficient of x_v in B⁺.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Commute.lean#L82-L84
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Commute.lean#L82-L84

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

theorem GeneralPieces.GenF.DD_sel (rd : Bool) (i v : X) : DD rd i (sel rd 0 JpV v) = emb (kq rd i v) := by sorry
