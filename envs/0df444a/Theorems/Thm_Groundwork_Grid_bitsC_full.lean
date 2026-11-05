-- Prove2me | Theorems.Thm_Groundwork_Grid_bitsC_full
-- name    : Groundwork.Grid.bitsC_full
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:37:12.588508+00:00
-- url     : https://prove2.me/theorems/bc16862f-c24b-400d-ac8f-98ae540ca1ba
-- title:
--   Grid: bits C full
-- statement:
--   The Grid construction uses the bits C full property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CutWord.lean#L48-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CutWord.lean#L48-L48

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Sparse
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_StepMachines_Math_CutWord
set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (tb capW)

theorem Groundwork.Grid.bitsC_full (n : ℕ) : (bitsC n).Full := by sorry
