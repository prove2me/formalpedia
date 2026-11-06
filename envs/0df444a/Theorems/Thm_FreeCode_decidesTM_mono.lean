-- Prove2me | Theorems.Thm_FreeCode_decidesTM_mono
-- name    : FreeCode.decidesTM_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:28:45.447821+00:00
-- url     : https://prove2.me/theorems/30c22e2d-41ab-47fb-874b-06cbd48d15f3
-- title:
--   Free Code: decides TM mono
-- statement:
--   A machine that decides k-SAT on codes in time t decides it in every larger time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Behind.lean#L70-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Behind.lean#L70-L73

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Code
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_ToTuring_Machine_EndTM
import Mathlib.Tactic
import Definitions.Def_FreeCode_Behind
set_option autoImplicit false
section
section
open FreeCode
open Groundwork Groundwork.Prog Paper SplitSat

theorem FreeCode.decidesTM_mono {k : ℕ} {M : Turing.TM2ComputableAux Bool Bool} {t t' : ℕ → ℕ} (ht : ∀ n, t n ≤ t' n) (h : SatFree.DecidesTM k M t) :
    SatFree.DecidesTM k M t' := by sorry
