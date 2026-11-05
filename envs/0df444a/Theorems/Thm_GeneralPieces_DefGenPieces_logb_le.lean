-- Prove2me | Theorems.Thm_GeneralPieces_DefGenPieces_logb_le
-- name    : GeneralPieces.DefGenPieces.logb_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:47:15.97857+00:00
-- url     : https://prove2.me/theorems/62e94d37-19ca-4535-9e77-35bdcccaa4cb
-- title:
--   Def Gen Pieces: logb le
-- statement:
--   log(2λ) ≤ λ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/DefGenPieces/Conv.lean#L51-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/DefGenPieces/Conv.lean#L51-L61

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

theorem GeneralPieces.DefGenPieces.logb_le {lam : ℕ} (hl : 1 ≤ lam) : Real.logb 2 (2 * lam) ≤ lam := by sorry
