-- Prove2me | Theorems.Thm_GeneralPieces_DefGenPieces_sum_bitsOf
-- name    : GeneralPieces.DefGenPieces.sum_bitsOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:39:04.617564+00:00
-- url     : https://prove2.me/theorems/9f5a4050-2202-4827-b8b6-b80d31ba073a
-- title:
--   Def Gen Pieces: sum bits Of
-- statement:
--   A sum over all strings of n bits, as functions, is the sum over all words of n bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/DefGenPieces/ToPure.lean#L26-L28
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/DefGenPieces/ToPure.lean#L26-L28

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Definitions.Def_GeneralPieces_DefGenPieces_ToPure
set_option autoImplicit false
section
section
open GeneralPieces
open Finset Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen AppRunningTime
open GeneralPieces.DefGenPieces
open Trim

theorem GeneralPieces.DefGenPieces.sum_bitsOf {n : ℕ} (G : List Bool → ℤ) : ∑ θ : Pieces.Bits n, G (bitsOf θ) = ∑ w ∈ words n, G w := by sorry
