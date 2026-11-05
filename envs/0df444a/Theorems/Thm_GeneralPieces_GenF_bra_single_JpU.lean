-- Prove2me | Theorems.Thm_GeneralPieces_GenF_bra_single_JpU
-- name    : GeneralPieces.GenF.bra_single_JpU
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:06:30.633189+00:00
-- url     : https://prove2.me/theorems/8778c30f-b281-4e37-9833-69d540b384d2
-- title:
--   Gen F: bra single Jp U
-- statement:
--   The coefficient of t_l in the part of J_n^+(u) with l ≤ E is C(l−1, n−1)·u^{l−n} for l ≤ E.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L317-L333
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L317-L333

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

theorem GeneralPieces.GenF.bra_single_JpU {E l : ℕ} (hl : l ≤ E) (n : ℕ) : bra {l} (HahnSeries.C (JpU E n)) = (bet n l : ℚ) • mo ((l : ℤ) - n) 0 := by sorry
