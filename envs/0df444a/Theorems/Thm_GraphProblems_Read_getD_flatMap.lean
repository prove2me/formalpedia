-- Prove2me | Theorems.Thm_GraphProblems_Read_getD_flatMap
-- name    : GraphProblems.Read.getD_flatMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:41:08.584854+00:00
-- url     : https://prove2.me/theorems/ec6927ee-d232-422d-b390-75a5aeca6b29
-- title:
--   Read: get D flat Map
-- statement:
--   In a list of rows of length n written one after the other, the entry i·n + j is the entry j of
--   row i.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Read.lean#L41-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Read.lean#L41-L53

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_GraphProblems_Read
set_option autoImplicit false
section
section
open GraphProblems
open GraphProblems.Read

theorem GraphProblems.Read.getD_flatMap {α β : Type} (f : α → List β) (n : ℕ) (d : β) {j : ℕ} (hj : j < n) :
    ∀ (L : List α) (_ : ∀ a ∈ L, (f a).length = n) (i : ℕ), (L.flatMap f).getD (i * n + j) d = (L[i]?.map fun a => (f a).getD j d).getD d
  := by sorry
