-- Prove2me | Theorems.Thm_GeneralPieces_to_par_one
-- name    : GeneralPieces.to_par_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:49:48.817205+00:00
-- url     : https://prove2.me/theorems/e3675f1a-9186-40da-9207-74bd816ae3f6
-- title:
--   General Pieces: to par one
-- statement:
--   Pieces with parameters (ρ, c) and c^row, c^col ≤ 2λ: the recursion has them with m = 1 and with
--   the same constant c.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/DefGenPieces/Conv.lean#L169-L171
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/DefGenPieces/Conv.lean#L169-L171

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
open DefGenPieces Trim
variable {ρ : ℝ} {c : ℕ} {P : PiecesF} {A : (lam : ℕ) → ℕ → Pieces.Four lam} {val : ValQ → ℤ}

theorem GeneralPieces.to_par_one (h : IsPieces ρ c P A val) (hcap : ∀ tr lam i, 1 ≤ lam → i < P.cnt 0 lam → P.cap tr 0 lam i ≤ 2 * lam) :
    Par (atZero P c 1) ρ c ∧ (atZero P c 1).Keeps ∧ (atZero P c 1).m = 1 := by sorry
