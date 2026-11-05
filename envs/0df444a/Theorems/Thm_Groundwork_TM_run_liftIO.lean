-- Prove2me | Theorems.Thm_Groundwork_TM_run_liftIO
-- name    : Groundwork.TM.run_liftIO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:12:02.519887+00:00
-- url     : https://prove2.me/theorems/0efd494a-e98c-4e68-b5c1-459146502ab9
-- title:
--   TM: run lift IO
-- statement:
--   Runs over the work stacks are runs of the final machine.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Lift.lean#L75-L83
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Lift.lean#L75-L83

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

theorem Groundwork.TM.run_liftIO {Λ σ : Type} (W : List Bool) {M : Λ → TM2.Stmt (fun _ : Stk => Sym) Λ σ} :
    ∀ {n : ℕ} {a b : TM2.Cfg (fun _ : Stk => Sym) Λ σ}, Run (TM2.step M) a n b →
      Run (TM2.step fun l => liftIO (M l)) (liftCfg W a) n (liftCfg W b)
  := by sorry
