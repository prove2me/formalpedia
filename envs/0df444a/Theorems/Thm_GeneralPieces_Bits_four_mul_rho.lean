-- Prove2me | Theorems.Thm_GeneralPieces_Bits_four_mul_rho
-- name    : GeneralPieces.Bits.four_mul_rho
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:26:56.104269+00:00
-- url     : https://prove2.me/theorems/281fd55b-e5d0-4106-80f0-3e222efdcded
-- title:
--   Bits: four mul rho
-- statement:
--   4ρ = 2√2 for ρ = 1/√2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L264-L266
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L264-L266

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Sizes
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_GeneralPieces_Ring_Bits
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Bits
open AppHalfPieces Finset Partitions Real GeneralPieces.Lex GeneralPieces.Sizes
variable {B C : ℝ}

theorem GeneralPieces.Bits.four_mul_rho : 4 * (1 / √(2 : ℝ)) = 2 * √2 := by sorry
