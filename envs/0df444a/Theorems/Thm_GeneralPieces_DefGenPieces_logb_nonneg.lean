-- Prove2me | Theorems.Thm_GeneralPieces_DefGenPieces_logb_nonneg
-- name    : GeneralPieces.DefGenPieces.logb_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:53:22.699022+00:00
-- url     : https://prove2.me/theorems/fc2038c3-ce03-4cfd-8ff3-57c09a091e2c
-- title:
--   Def Gen Pieces: logb nonneg
-- statement:
--   log(2λ) ≥ 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/DefGenPieces/Conv.lean#L45-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/DefGenPieces/Conv.lean#L45-L48

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

theorem GeneralPieces.DefGenPieces.logb_nonneg {lam : ℕ} (hl : 1 ≤ lam) : 0 ≤ Real.logb 2 (2 * lam) := by sorry
