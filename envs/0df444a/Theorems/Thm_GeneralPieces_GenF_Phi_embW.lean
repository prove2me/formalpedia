-- Prove2me | Theorems.Thm_GeneralPieces_GenF_Phi_embW
-- name    : GeneralPieces.GenF.Phi_embW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:08:25.125511+00:00
-- url     : https://prove2.me/theorems/3d8d204f-7252-494f-80de-3ffbc68588d8
-- title:
--   Gen F: Phi emb W
-- statement:
--   e^{A⁻} fixes the series without any t_k.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L122-L125
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L122-L125

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

theorem GeneralPieces.GenF.Phi_embW (rd : Bool) (e : PS) : Phi rd (embW e) = embW e := by sorry
