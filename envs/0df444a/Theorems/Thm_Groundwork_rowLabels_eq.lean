-- Prove2me | Theorems.Thm_Groundwork_rowLabels_eq
-- name    : Groundwork.rowLabels_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:15:54.584007+00:00
-- url     : https://prove2.me/theorems/7f6a0b14-134f-4f68-aaf5-a5fbbbdde465
-- title:
--   Groundwork: row Labels eq
-- statement:
--   At least i singlets: at most n − i states other than the singlet.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Sparse.lean#L244-L250
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Sparse.lean#L244-L250

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

theorem Groundwork.rowLabels_eq {n i : ℕ} (h : i ≤ n) : rowLabels n i = sparseLab (true, true) n (n - i) := by sorry
