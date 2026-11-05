-- Prove2me | Theorems.Thm_GeneralPieces_Series_cfP_epsP_pow
-- name    : GeneralPieces.Series.cfP_epsP_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:19:14.7486+00:00
-- url     : https://prove2.me/theorems/807f6791-3abb-4fd1-bab7-bb71472d6be8
-- title:
--   Series: cf P eps P pow
-- statement:
--   In ε₊^N the coefficient of ω₁^{−N}·ω₂^0 is 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Constant.lean#L123-L129
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Constant.lean#L123-L129

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

theorem GeneralPieces.Series.cfP_epsP_pow (N : ℕ) : cfP (epsP ^ N) (-(N : ℤ)) 0 = 1 := by sorry
