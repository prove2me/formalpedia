-- Prove2me | Theorems.Thm_GeneralPieces_atZero_keeps
-- name    : GeneralPieces.atZero_keeps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:36:18.084889+00:00
-- url     : https://prove2.me/theorems/2e644187-72b6-4632-9ac9-d58652ce60a2
-- title:
--   General Pieces: at Zero keeps
-- statement:
--   The programs read at h = 0 are polynomial-time (`PiecesF.Keeps`), by the time clauses of the
--   definition.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/DefGenPieces/Conv.lean#L158-L165
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/DefGenPieces/Conv.lean#L158-L165

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

theorem GeneralPieces.atZero_keeps (h : IsPieces ρ c P A val) (m : ℕ) : (atZero P c m).Keeps := by sorry
