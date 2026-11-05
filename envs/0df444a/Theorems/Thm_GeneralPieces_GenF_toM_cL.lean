-- Prove2me | Theorems.Thm_GeneralPieces_GenF_toM_cL
-- name    : GeneralPieces.GenF.toM_cL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:07:28.04425+00:00
-- url     : https://prove2.me/theorems/11412798-d6f2-4ee4-ad1c-5c0e3ab1bd72
-- title:
--   Gen F: to M c L
-- statement:
--   In 𝓛₋ (`rd = true`) it is the image of the same element of 𝓛.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/NormalL.lean#L51-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/NormalL.lean#L51-L52

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

theorem GeneralPieces.GenF.toM_cL (i : X) (r : ℤ) : toM (cL i r) = cS true i r := by sorry
