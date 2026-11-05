-- Prove2me | Theorems.Thm_GeneralPieces_trimV_cap_le
-- name    : GeneralPieces.trimV_cap_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:47:05.852063+00:00
-- url     : https://prove2.me/theorems/3087da16-f1ff-4146-8b37-bf55cd50eec7
-- title:
--   General Pieces: trim V cap le
-- statement:
--   All numbers of bits of the new programs are at most 2λ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/DefGenPieces/MayAssume.lean#L122-L122
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/DefGenPieces/MayAssume.lean#L122-L122

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

theorem GeneralPieces.trimV_cap_le (P : PiecesF) (val : ValQ → ℤ) (c : ℕ) (tr : Bool) (h lam i : ℕ) : (trimV P val c).cap tr h lam i ≤ 2 * lam := by sorry
