-- Prove2me | Theorems.Thm_Groundwork_PolyT_of_wd
-- name    : Groundwork.PolyT.of_wd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:45:26.797542+00:00
-- url     : https://prove2.me/theorems/667cdf8a-2f93-4895-9081-2c5f91d32798
-- title:
--   Poly T: of wd
-- statement:
--   Only words matter: if φ keeps the words of the inputs, and the words of g's values are those of
--   f ∘ φ, then g is
--   polynomial-time, computed by the same fragment as f. The types may differ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/PolyT.lean#L87-L94
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/PolyT.lean#L87-L94

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

theorem Groundwork.PolyT.of_wd {α β α' β' : Type} [Enc α] [Enc β] [Enc α'] [Enc β'] {f : α → β} (hf : PolyT f) {g : α' → β'}
    (φ : α' → α) (hφ : ∀ x, wd (φ x) = wd x) (hg : ∀ x, wd (g x) = wd (f (φ x))) : PolyT g := by sorry
