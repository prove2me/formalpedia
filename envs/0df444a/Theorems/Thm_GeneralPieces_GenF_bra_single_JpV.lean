-- Prove2me | Theorems.Thm_GeneralPieces_GenF_bra_single_JpV
-- name    : GeneralPieces.GenF.bra_single_JpV
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:33:09.246683+00:00
-- url     : https://prove2.me/theorems/8e2c9da0-badf-4e63-b5dd-75a2b90b8350
-- title:
--   Gen F: bra single Jp V
-- statement:
--   The coefficient of t_l in J_n^+(v) is C(l−1, n−1)·v^{l−n}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L287-L299
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L287-L299

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

theorem GeneralPieces.GenF.bra_single_JpV (l n : ℕ) : bra {l} (JpV n) = (bet n l : ℚ) • mo 0 ((l : ℤ) - n) := by sorry
