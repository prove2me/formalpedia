-- Prove2me | Theorems.Thm_Groundwork_PolyT_tagF_within
-- name    : Groundwork.PolyT.tagF_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:51:47.90421+00:00
-- url     : https://prove2.me/theorems/70164422-c490-4e6c-a5a0-48a30683fc41
-- title:
--   Poly T: tag F within
-- statement:
--   The Poly T construction uses the tag F within property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Cases.lean#L113-L119
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Cases.lean#L113-L119

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Closure_Cases
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
open TM Turing
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem Groundwork.PolyT.tagF_within (b : Bool) (x : V) (M A B N : List Sym) :
    (tagF b).Within (st (code x ++ M) A B N) (2 * (code x).length + 9) (st (code (.cons (.bit b) x) ++ M) A B N) := by sorry
