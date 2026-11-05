-- Prove2me | Theorems.Thm_GeneralPieces_GenF_stNeq
-- name    : GeneralPieces.GenF.stNeq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:08:58.050069+00:00
-- url     : https://prove2.me/theorems/70c985cc-9f8c-4deb-a656-5dd20e776ae5
-- title:
--   Gen F: st Neq
-- statement:
--   The differential equation of ⟨𝒩⟩, as the statement from which the coefficients of ⟨𝒩⟩ are read
--   off.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L220-L220
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L220-L220

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_GeneralPieces_GenF_Normal
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial

theorem GeneralPieces.GenF.stNeq : StNeq := by sorry
