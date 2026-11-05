-- Prove2me | Theorems.Thm_Groundwork_PolyT_of
-- name    : Groundwork.PolyT.of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:45:35.612338+00:00
-- url     : https://prove2.me/theorems/df54ce9a-43de-461d-96d2-465f278b35be
-- title:
--   Poly T: of
-- statement:
--   How to prove PolyT: a fragment, a polynomial bound on its steps, a polynomial bound on the
--   length of the result.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/PolyT.lean#L62-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/PolyT.lean#L62-L70

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

theorem Groundwork.PolyT.of {α β : Type} [Enc α] [Enc β] {f : α → β} (P : Fr) {t s : ℕ → ℕ} (ht : PB t) (hs : PB s)
    (h : ∀ (x : α) (M A B N : List Sym), P.Within (st (wd x ++ M) A B N) (t (len x)) (st (wd (f x) ++ M) A B N))
    (hl : ∀ x, len (f x) ≤ s (len x)) : PolyT f := by sorry
