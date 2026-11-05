-- Prove2me | Theorems.Thm_Groundwork_PolyT_dropWhile
-- name    : Groundwork.PolyT.dropWhile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:27:16.246327+00:00
-- url     : https://prove2.me/theorems/fd6bb3b8-48ce-40ce-a994-7738eb20eed4
-- title:
--   Poly T: drop While
-- statement:
--   The list without its longest prefix whose elements pass a test.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List3.lean#L85-L89
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List3.lean#L85-L89

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_List2
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.ProdSigma
import Definitions.Def_ToTuring_Lib_List3
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem Groundwork.PolyT.dropWhile {f : α → β → Bool} {l : α → List β} (hf : PolyT fun p : α × β => f p.1 p.2) (hl : PolyT l) :
    PolyT (fun x => (l x).dropWhile (f x)) := by sorry
