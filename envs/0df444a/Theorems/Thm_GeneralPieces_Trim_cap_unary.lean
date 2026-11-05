-- Prove2me | Theorems.Thm_GeneralPieces_Trim_cap_unary
-- name    : GeneralPieces.Trim.cap_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:34:07.476965+00:00
-- url     : https://prove2.me/theorems/7109e549-cf37-4449-85ff-1e8ef8f024ec
-- title:
--   Trim: cap unary
-- statement:
--   The number of bits of a factorization of P, with h and λ in unary and the number of the piece in
--   binary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Trim/Cert.lean#L36-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Trim/Cert.lean#L36-L38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Trim_Prog
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_GeneralPieces_Trim_Cert
set_option autoImplicit false
section
section
open GeneralPieces
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen
open GeneralPieces.Trim
variable {α : Type} [Enc α] {P : PiecesF}

theorem GeneralPieces.Trim.cap_unary (hP : P.Keeps) {tr : α → Bool} {h lam i : α → ℕ} (ht : PolyT tr) (hh : Unary h) (hl : Unary lam) (hi : PolyT i) :
    Unary fun x => P.cap (tr x) (h x) (lam x) (i x) := by sorry
