-- Prove2me | Theorems.Thm_GeneralPieces_DefGenPieces_abs_lt
-- name    : GeneralPieces.DefGenPieces.abs_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:37:47.003322+00:00
-- url     : https://prove2.me/theorems/ad7f5248-218e-442a-a78c-0573e38cdcdf
-- title:
--   Def Gen Pieces: abs lt
-- statement:
--   «At most 2^b» with b ≤ (2λ)^c is «below 2^{(2λ)^{c'}}» for c' > c.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/DefGenPieces/Conv.lean#L41-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/DefGenPieces/Conv.lean#L41-L42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppRunningTimeStatement
import Definitions.Def_GeneralPieces_Trim_Cert
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
set_option autoImplicit false
section
section
open GeneralPieces
open Finset Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen AppRunningTime
open GeneralPieces.DefGenPieces

theorem GeneralPieces.DefGenPieces.abs_lt {z : ℤ} {b lam c c' : ℕ} (hz : |z| ≤ 2 ^ b) (hb : b ≤ (2 * lam) ^ c) (hl : 1 ≤ lam) (hc : c < c') : |z| < 2 ^ (2 * lam) ^ c' := by sorry
