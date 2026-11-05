-- Prove2me | Theorems.Thm_GeneralPieces_Series_bet_eq_zero
-- name    : GeneralPieces.Series.bet_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:07:34.158657+00:00
-- url     : https://prove2.me/theorems/232fc0ac-7ecc-489c-a416-b1f775e21ed3
-- title:
--   Series: bet eq zero
-- statement:
--   C(l−1, n−1) = 0 for l < n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Constant.lean#L35-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Constant.lean#L35-L39

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

theorem GeneralPieces.Series.bet_eq_zero {n l : ℕ} (h : l < n) : bet n l = 0 := by sorry
