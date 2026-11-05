-- Prove2me | Theorems.Thm_GeneralPieces_trimV_isPieces
-- name    : GeneralPieces.trimV_isPieces
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:47:23.437194+00:00
-- url     : https://prove2.me/theorems/24477dd5-4605-42f8-aea8-da116d771ab7
-- title:
--   General Pieces: trim V is Pieces
-- statement:
--   «We may and do assume c_row, c_col ≤ 2λ»: the new programs are pieces with the same parameters
--   (ρ, c), the same functions A_i and the same program for their values.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/DefGenPieces/MayAssume.lean#L61-L119
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/DefGenPieces/MayAssume.lean#L61-L119

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
variable {ρ : ℝ} {c : ℕ} {P : PiecesF} {A : (lam : ℕ) → ℕ → Pieces.Four lam} {val : ValQ → ℤ}

theorem GeneralPieces.trimV_isPieces (h : IsPieces ρ c P A val) : IsPieces ρ c (trimV P val c) A val := by sorry
