-- Prove2me | Theorems.Thm_Groundwork_PolyT_elim
-- name    : Groundwork.PolyT.elim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:45:21.509067+00:00
-- url     : https://prove2.me/theorems/425c3921-80ab-4576-bcde-6ed28c9ab78a
-- title:
--   Poly T: elim
-- statement:
--   How to use PolyT: one monotone polynomial bound for the steps and for the length of the result.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/PolyT.lean#L73-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/PolyT.lean#L73-L77

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Enc
import Definitions.Def_ToTuring_TM_Ops
import Definitions.Def_ToTuring_Bound
import Mathlib.Tactic.FunProp
import Definitions.Def_ToTuring_PolyT
set_option autoImplicit false
section
section
open Groundwork
open TM

theorem Groundwork.PolyT.elim {α β : Type} [Enc α] [Enc β] {f : α → β} (h : PolyT f) : ∃ (P : Fr) (t : ℕ → ℕ), PB t ∧ Monotone t ∧
    (∀ (x : α) (M A B N : List Sym), P.Within (st (wd x ++ M) A B N) (t (len x)) (st (wd (f x) ++ M) A B N)) ∧
    ∀ x, len (f x) ≤ t (len x) := by sorry
