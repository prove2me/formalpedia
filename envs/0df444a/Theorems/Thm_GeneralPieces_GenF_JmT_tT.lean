-- Prove2me | Theorems.Thm_GeneralPieces_GenF_JmT_tT
-- name    : GeneralPieces.GenF.JmT_tT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:08:28.322235+00:00
-- url     : https://prove2.me/theorems/cb16d0a0-c365-49ef-9dc2-507f4022eaa0
-- title:
--   Gen F: Jm T t T
-- statement:
--   J_n^-(u) maps t_k to k·C(−k−1, n−1)·u^{−k−n}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L141-L144
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L141-L144

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

theorem GeneralPieces.GenF.JmT_tT (n k : ℕ) : JmT n (tT k) = emb ((k : ℚ) • ((bet n (-(k : ℤ)) : ℚ) • mo (-(k : ℤ) - n) 0)) := by sorry
