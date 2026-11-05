-- Prove2me | Theorems.Thm_Groundwork_PolyT_tagHead_eq
-- name    : Groundwork.PolyT.tagHead_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:54:37.82227+00:00
-- url     : https://prove2.me/theorems/6c2871dd-4d0c-4e5c-833a-a51f9bbc8dcc
-- title:
--   Poly T: tag Head eq
-- statement:
--   The Poly T construction uses the tag Head eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Cases.lean#L42-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Cases.lean#L42-L45

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

theorem Groundwork.PolyT.tagHead_eq (b : Bool) (M A B N : List Sym) :
    TM2.stepAux tagHead none (st (.bit b :: M) A B N) = ⟨some b, none, st M A B N⟩ := by sorry
