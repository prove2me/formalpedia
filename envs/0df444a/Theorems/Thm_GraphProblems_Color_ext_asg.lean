-- Prove2me | Theorems.Thm_GraphProblems_Color_ext_asg
-- name    : GraphProblems.Color.ext_asg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:32:02.010173+00:00
-- url     : https://prove2.me/theorems/fa415d50-afa1-4fed-ae2c-8c724d8927d6
-- title:
--   Color: ext asg
-- statement:
--   The Color construction uses the ext asg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Color.lean#L79-L85
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Color.lean#L79-L85

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

theorem GraphProblems.Color.ext_asg {n k : ℕ} (col : Fin n → Fin k) (v : Fin n) {c : ℕ} (hc : c < k) : ext (asg col) (v * k + c) = decide ((col v).val = c) := by sorry
