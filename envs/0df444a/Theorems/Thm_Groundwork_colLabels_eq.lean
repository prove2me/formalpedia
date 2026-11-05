-- Prove2me | Theorems.Thm_Groundwork_colLabels_eq
-- name    : Groundwork.colLabels_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:16:03.699098+00:00
-- url     : https://prove2.me/theorems/e0fd2bfe-afb3-4024-b17a-b94e9b1ac89d
-- title:
--   Groundwork: col Labels eq
-- statement:
--   At most i states other than Φ⁺: the label set for columns.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Sparse.lean#L253-L253
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Sparse.lean#L253-L253

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_StepMachines_Math_CodeMore
import Definitions.Def_StepMachines_Math_Sparse
set_option autoImplicit false
section
section
open Groundwork
open Finset
open Groundwork.Prog (tb capW)

theorem Groundwork.colLabels_eq (n i : ℕ) : colLabels n i = sparseLab (false, false) n i := by sorry
