-- Prove2me | Theorems.Thm_GeneralPieces_GenF_toP_cL
-- name    : GeneralPieces.GenF.toP_cL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:07:31.779549+00:00
-- url     : https://prove2.me/theorems/8d86bf83-f9bc-4710-9ac5-38090b0f9bf4
-- title:
--   Gen F: to P c L
-- statement:
--   In 𝓛₊ (`rd = false`) the factor is the image of that element of 𝓛.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/NormalL.lean#L47-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/NormalL.lean#L47-L48

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_NormalL
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson

theorem GeneralPieces.GenF.toP_cL (i : X) (r : ℤ) : toP (cL i r) = cS false i r := by sorry
