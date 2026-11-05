-- Prove2me | Theorems.Thm_GraphProblems_Color_exists_coloring
-- name    : GraphProblems.Color.exists_coloring
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T18:41:50.857918+00:00
-- url     : https://prove2.me/theorems/b919e451-d607-43fb-a855-9c3cd0d6deb4
-- title:
--   Color: exists coloring
-- statement:
--   Every satisfying assignment is the assignment of a proper coloring.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Color.lean#L108-L150
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Color.lean#L108-L150

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Blocks
import Definitions.Def_GraphProblems_Color
set_option autoImplicit false
section
section
open GraphProblems
open Groundwork Groundwork.Prog CountKSat Finset
open GraphProblems.Color
open Blocks

theorem GraphProblems.Color.exists_coloring (hAdj : StAdj) {n k : ℕ} (G : SimpleGraph (Fin n)) (a : Fin (n * k) → Bool) (ha : Sat (ext a) (colorF k n (matrix G))) :
    ∃ col : G.Coloring (Fin k), asg col = a := by sorry
