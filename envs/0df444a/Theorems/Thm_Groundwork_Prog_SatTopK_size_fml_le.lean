-- Prove2me | Theorems.Thm_Groundwork_Prog_SatTopK_size_fml_le
-- name    : Groundwork.Prog.SatTopK.size_fml_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:36:50.538091+00:00
-- url     : https://prove2.me/theorems/fefb4370-18d3-4b06-bd7d-90592e48b90e
-- title:
--   Sat Top K: size fml le
-- statement:
--   A bound on the size of a formula of at most m clauses of at most k literals with variables below
--   n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Top/Sat.lean#L61-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Top/Sat.lean#L61-L63

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_StepMachines_Prog_Comb
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Math_SparsifyTree
import Definitions.Def_KSatStatement
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_WidthK_Top_Sat
set_option autoImplicit false
section
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK
open Groundwork.Sparsify (leaves)

theorem Groundwork.Prog.SatTopK.size_fml_le {k : ℕ} {x : Fml} {m n : ℕ} (hm : x.length ≤ m) (hx : ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) :
    size x ≤ m * (k * (n + 2 + 1) + 1 + 1) + 1 := by sorry
