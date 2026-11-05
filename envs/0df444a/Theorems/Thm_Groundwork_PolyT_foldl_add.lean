-- Prove2me | Theorems.Thm_Groundwork_PolyT_foldl_add
-- name    : Groundwork.PolyT.foldl_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:23:26.014207+00:00
-- url     : https://prove2.me/theorems/65bf943e-3aed-4e59-a7fc-e6c409fe4e1b
-- title:
--   Poly T: foldl add
-- statement:
--   The fold when every step adds at most b(len x) to the length, b a polynomial bound.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Fold.lean#L159-L182
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Fold.lean#L159-L182

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Closure_Cases
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_ToTuring_Closure_Fold
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
open TM Turing
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem Groundwork.PolyT.foldl_add {l : α → List ε} {a : α → γ} {g : α → γ → ε → γ} (hl : PolyT l) (ha : PolyT a)
    (hg : PolyT fun p : α × γ × ε => g p.1 p.2.1 p.2.2)
    (hB : ∃ b, PB b ∧ ∀ x c, ∀ e ∈ l x, len (g x c e) ≤ len c + b (len x)) :
    PolyT (fun x => (l x).foldl (g x) (a x)) := by sorry
