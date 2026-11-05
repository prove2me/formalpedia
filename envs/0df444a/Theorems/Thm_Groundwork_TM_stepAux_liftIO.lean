-- Prove2me | Theorems.Thm_Groundwork_TM_stepAux_liftIO
-- name    : Groundwork.TM.stepAux_liftIO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:11:57.45703+00:00
-- url     : https://prove2.me/theorems/e6cd5981-1d78-445f-a075-df2f4297cb7c
-- title:
--   TM: step Aux lift IO
-- statement:
--   A statement, lifted to the final machine, does what it does over the work stacks alone, and does
--   not touch the bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Lift.lean#L63-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Lift.lean#L63-L72

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Stacks
import Definitions.Def_ToTuring_Machine_Lift
set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing

theorem Groundwork.TM.stepAux_liftIO {Λ σ : Type} (W : List Bool) (q : TM2.Stmt (fun _ : Stk => Sym) Λ σ) (v : σ) (S : Stk → List Sym) :
    TM2.stepAux (liftIO q) v (withIO W S) = liftCfg W (TM2.stepAux q v S) := by sorry
