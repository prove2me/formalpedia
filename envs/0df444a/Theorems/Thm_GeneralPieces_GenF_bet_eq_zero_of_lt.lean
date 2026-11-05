-- Prove2me | Theorems.Thm_GeneralPieces_GenF_bet_eq_zero_of_lt
-- name    : GeneralPieces.GenF.bet_eq_zero_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:06:18.438399+00:00
-- url     : https://prove2.me/theorems/1a639823-cb0f-4fe3-80d9-258a6547b856
-- title:
--   Gen F: bet eq zero of lt
-- statement:
--   C(l−1, n−1) = 0 for l < n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L264-L268
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L264-L268

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial

theorem GeneralPieces.GenF.bet_eq_zero_of_lt {n l : ℕ} (h : l < n) : bet n (l : ℤ) = 0 := by sorry
