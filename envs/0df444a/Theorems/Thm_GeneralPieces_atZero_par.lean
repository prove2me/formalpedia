-- Prove2me | Theorems.Thm_GeneralPieces_atZero_par
-- name    : GeneralPieces.atZero_par
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:35:29.525791+00:00
-- url     : https://prove2.me/theorems/acebf86c-1e81-457c-b0b4-f08d53c56d8a
-- title:
--   General Pieces: at Zero par
-- statement:
--   Pieces with parameters (ρ, c) all of whose numbers of bits are at most 2·m·λ give `Par` with
--   every constant c' ≥ c, m.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/DefGenPieces/Conv.lean#L135-L154
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/DefGenPieces/Conv.lean#L135-L154

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

theorem GeneralPieces.atZero_par (h : IsPieces ρ c P A val) {m c' : ℕ} (hm : 1 ≤ m) (hcap : ∀ tr lam i, 1 ≤ lam → i < P.cnt 0 lam → P.cap tr 0 lam i ≤ 2 * m * lam)
    (hc : c ≤ c') (hmc : m ≤ c') : Par (atZero P c m) ρ c' := by sorry
