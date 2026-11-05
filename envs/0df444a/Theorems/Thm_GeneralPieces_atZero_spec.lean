-- Prove2me | Theorems.Thm_GeneralPieces_atZero_spec
-- name    : GeneralPieces.atZero_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:35:12.477819+00:00
-- url     : https://prove2.me/theorems/91e80bee-52f6-4877-a57a-29547d7c4bbd
-- title:
--   General Pieces: at Zero spec
-- statement:
--   The programs read at h = 0 are pieces in the sense of the recursion, at every h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/DefGenPieces/Conv.lean#L124-L131
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/DefGenPieces/Conv.lean#L124-L131

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

theorem GeneralPieces.atZero_spec (h : IsPieces ρ c P A val) {m : ℕ} (hm : 1 ≤ m) (hcap : ∀ tr lam i, 1 ≤ lam → i < P.cnt 0 lam → P.cap tr 0 lam i ≤ 2 * m * lam)
    (hh : ℕ) {lam : ℕ} (hl : 1 ≤ lam) : (atZero P c m).Spec hh lam := by sorry
