-- Prove2me | Theorems.Thm_GeneralPieces_Series_Expansion_fP_vac
-- name    : GeneralPieces.Series.Expansion.fP_vac
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:19:06.887854+00:00
-- url     : https://prove2.me/theorems/dd07443e-82a7-4ab8-917b-d627a070c7a6
-- title:
--   Expansion: f P vac
-- statement:
--   For E = 0: f₊ = G·ε₊^H.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Constant.lean#L119-L120
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Constant.lean#L119-L120

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_ReadOff
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_GeneralPieces_Series_Constant
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset
variable {a b : List ℕ} {G : ℚ}

theorem GeneralPieces.Series.Expansion.fP_vac (X : Expansion a b G 0 0) : fP a b 0 0 = G • epsP ^ (a.sum + b.sum) := by sorry
