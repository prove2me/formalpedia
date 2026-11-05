-- Prove2me | Theorems.Thm_GeneralPieces_GenF_DD_tT
-- name    : GeneralPieces.GenF.DD_tT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:08:23.295959+00:00
-- url     : https://prove2.me/theorems/743bd4e2-ecb2-4077-b5e6-9a517a22464f
-- title:
--   Gen F: DD t T
-- statement:
--   The operator beside x_i in A⁻ maps t_k to k times the coefficient of x_i in 𝖠_k.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L147-L153
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L147-L153

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

theorem GeneralPieces.GenF.DD_tT (rd : Bool) (i : X) (k : ℕ) : DD rd i (tT k) = emb ((k : ℚ) • sel rd (fun n => (bet n (-(k : ℤ)) : ℚ) • mo (-(k : ℤ) - n) 0) 0 i) := by sorry
