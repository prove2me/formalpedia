-- Prove2me | Theorems.Thm_GeneralPieces_mayAssume
-- name    : GeneralPieces.mayAssume
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:18:11.57888+00:00
-- url     : https://prove2.me/theorems/d69b9d57-3027-49ae-9761-a9639cc9d4c9
-- title:
--   General Pieces: may Assume
-- statement:
--   «We may and do assume c_row, c_col ≤ 2λ», as stated in `AppRunningTimeStatement.lean`: the same
--   constant c, the same d, 𝓘 and A_i and the same program for the values.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/DefGenPieces/MayAssume.lean#L128-L129
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/DefGenPieces/MayAssume.lean#L128-L129

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_GeneralPieces_DefGenPieces_MayAssume
set_option autoImplicit false
section
section
open GeneralPieces
open Finset Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen AppRunningTime
open DefGenPieces Trim

theorem GeneralPieces.mayAssume : MayAssume := by sorry
