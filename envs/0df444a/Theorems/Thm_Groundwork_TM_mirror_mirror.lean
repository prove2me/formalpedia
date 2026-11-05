-- Prove2me | Theorems.Thm_Groundwork_TM_mirror_mirror
-- name    : Groundwork.TM.mirror_mirror
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:11:15.854049+00:00
-- url     : https://prove2.me/theorems/207ca1af-9cf2-48f1-bbe7-eb91a7ae233b
-- title:
--   TM: mirror mirror
-- statement:
--   The TM construction uses the mirror mirror property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Tree.lean#L51-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Tree.lean#L51-L53

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_ToTuring_TM_Tree
set_option autoImplicit false
section
section
open Groundwork Groundwork.TM

theorem Groundwork.TM.mirror_mirror (w : List Sym) : mirror (mirror w) = w := by sorry
