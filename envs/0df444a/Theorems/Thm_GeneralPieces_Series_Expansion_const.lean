-- Prove2me | Theorems.Thm_GeneralPieces_Series_Expansion_const
-- name    : GeneralPieces.Series.Expansion.const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:19:23.424665+00:00
-- url     : https://prove2.me/theorems/e1af70ee-39b1-4939-8e0f-7e39114bfb04
-- title:
--   Expansion: const
-- statement:
--   The constant: G = a[−h]b.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Constant.lean#L132-L136
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Constant.lean#L132-L136

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_ReadOff
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_GeneralPieces_Series_Constant
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset
variable {a b : List ℕ} {G : ℚ}

theorem GeneralPieces.Series.Expansion.const (X : Expansion a b G 0 0) (hb : Pos b) : G = op a (-(b.sum : ℤ)) 0 (b : Multiset ℕ) := by sorry
