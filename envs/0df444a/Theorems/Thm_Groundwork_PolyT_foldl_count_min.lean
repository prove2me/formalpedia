-- Prove2me | Theorems.Thm_Groundwork_PolyT_foldl_count_min
-- name    : Groundwork.PolyT.foldl_count_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:08:18.375834+00:00
-- url     : https://prove2.me/theorems/755af642-ca0e-4bd2-8e60-e7cf884d2352
-- title:
--   Poly T: foldl count min
-- statement:
--   Counting up to q along a list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L207-L220
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L207-L220

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_Nat2
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem Groundwork.PolyT.foldl_count_min {ι : Type} (q : ℕ) (l : List ι) (k : ℕ) (hk : k ≤ q) :
    l.foldl (fun (acc : List Unit) _ => if acc.length < q then () :: acc else acc) (List.replicate k ()) =
      List.replicate (min q (k + l.length)) () := by sorry
