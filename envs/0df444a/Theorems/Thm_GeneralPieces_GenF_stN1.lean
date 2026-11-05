-- Prove2me | Theorems.Thm_GeneralPieces_GenF_stN1
-- name    : GeneralPieces.GenF.stN1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:07:50.047933+00:00
-- url     : https://prove2.me/theorems/40416718-d149-4cd8-a525-2ae3c1eccafa
-- title:
--   Gen F: st N1
-- statement:
--   "the coefficient n_{μ'',ν''} of x^{μ''}x'^{ν''} in ⟨𝒩⟩ lies in 𝓛": its forms in 𝓛₊ and in 𝓛₋ are
--   the images of one element of 𝓛.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/NormalL.lean#L93-L118
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/NormalL.lean#L93-L118

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

theorem GeneralPieces.GenF.stN1 (hN : StNeq) : StN1 := by sorry
