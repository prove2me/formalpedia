-- Prove2me | Theorems.Thm_GeneralPieces_Series_bet_self
-- name    : GeneralPieces.Series.bet_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:18:47.590317+00:00
-- url     : https://prove2.me/theorems/ae1130bb-747f-4940-8d0f-bc6177768802
-- title:
--   Series: bet self
-- statement:
--   C(n−1, n−1) = 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Constant.lean#L42-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Constant.lean#L42-L44

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

theorem GeneralPieces.Series.bet_self {n : ℕ} (h : 1 ≤ n) : bet n n = 1 := by sorry
