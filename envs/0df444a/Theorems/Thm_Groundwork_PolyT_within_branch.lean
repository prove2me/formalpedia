-- Prove2me | Theorems.Thm_Groundwork_PolyT_within_branch
-- name    : Groundwork.PolyT.within_branch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:50:43.199196+00:00
-- url     : https://prove2.me/theorems/d45b7e6e-a5ab-4662-91d7-57686b478401
-- title:
--   Poly T: within branch
-- statement:
--   The head statement leads to the label b; then the fragment for b runs.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Cases.lean#L28-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Cases.lean#L28-L34

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Closure_Cases
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
open TM Turing
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem Groundwork.PolyT.within_branch {q : TM2.Stmt (fun _ : Stk => Sym) Bool (Option Sym)} {P Q : Fr} {S S₁ S' : Stk → List Sym} {t : ℕ}
    (b : Bool) (h : TM2.stepAux q none S = ⟨some b, none, S₁⟩) (hb : (bif b then P else Q).Within S₁ t S') :
    (Frag.branch q P Q).Within S (t + 1) S' := by sorry
