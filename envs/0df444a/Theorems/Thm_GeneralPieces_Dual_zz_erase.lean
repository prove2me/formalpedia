-- Prove2me | Theorems.Thm_GeneralPieces_Dual_zz_erase
-- name    : GeneralPieces.Dual.zz_erase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:36:07.496118+00:00
-- url     : https://prove2.me/theorems/b87db0ec-b3e3-4412-a6fc-d68633d229d6
-- title:
--   Dual: zz erase
-- statement:
--   z_ν = n·m_n(ν)·z_{ν−n}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L428-L438
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L428-L438

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces

theorem GeneralPieces.Dual.zz_erase {ν : Ptn} {n : ℕ+} (hn : n ∈ ν) : zz ν = (n : ℕ) * ν.count n * zz (ν.erase n) := by sorry
