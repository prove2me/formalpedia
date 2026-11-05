-- Prove2me | Theorems.Thm_Groundwork_TM_run_inside
-- name    : Groundwork.TM.run_inside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:11:51.432849+00:00
-- url     : https://prove2.me/theorems/21f75d69-88fb-4f44-9163-eb1466805640
-- title:
--   TM: run inside
-- statement:
--   Inside at least one open bracket, an item is moved and the loop goes on, the count as before.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Move.lean#L155-L170
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Move.lean#L155-L170

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Rename
import Definitions.Def_ToTuring_TM_Stacks
import Definitions.Def_ToTuring_TM_Move
set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing

theorem Groundwork.TM.run_inside (p₁ p₂ : Bool) : ∀ (x : V) (A B₁ B₂ C : List Sym),
    Run (TM2.step (mvM p₁ p₂)) ⟨some .loop, none, st4 (code x ++ A) B₁ B₂ (.R :: C)⟩ (code x).length
      ⟨some .loop, none, st4 A (putIf p₁ (mirror (code x)) B₁) (putIf p₂ (mirror (code x)) B₂) (.R :: C)⟩
  := by sorry
