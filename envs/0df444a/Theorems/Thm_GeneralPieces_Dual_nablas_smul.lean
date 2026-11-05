-- Prove2me | Theorems.Thm_GeneralPieces_Dual_nablas_smul
-- name    : GeneralPieces.Dual.nablas_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:24:57.759298+00:00
-- url     : https://prove2.me/theorems/90dbbdb3-60ba-4bc8-8a62-dc03b90a3e42
-- title:
--   Dual: nablas smul
-- statement:
--   The Dual construction uses the nablas smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L377-L380
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L377-L380

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

theorem GeneralPieces.Dual.nablas_smul (ks : List ℤ) (q : ℚ) (f : V) : nablas ks (q • f) = q • nablas ks f := by sorry
