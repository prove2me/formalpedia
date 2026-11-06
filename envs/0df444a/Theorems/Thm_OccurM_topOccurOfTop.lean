-- Prove2me | Theorems.Thm_OccurM_topOccurOfTop
-- name    : OccurM.topOccurOfTop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:08:02.484362+00:00
-- url     : https://prove2.me/theorems/562e46c3-2aaf-449b-a246-cfaf6271e0fd
-- title:
--   Occur M: top Occur Of Top
-- statement:
--   From the bound in m for the named top level on formulas in which every variable occurs to the
--   bound for the same top level after the named preparation, for both codes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Top.lean#L102-L106
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Top.lean#L102-L106

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_OccurM_TiedDefs
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_OccurM_Prep
import Definitions.Def_OccurM_Arith
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_VariableBound_Paper_Rename_Code
import Definitions.Def_VariableBound_Paper_Rename_Cert
import Definitions.Def_OccurM_Top
set_option autoImplicit false
section
section
open OccurM
open Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Turing MainTheoremForms ClausesOccur VariableBound.Rename
open Sat3 (CNF)
variable {Idx : Type} [Enc Idx] {S : Solver Idx} {pick : U → U × Idx} {α : ℝ}

theorem OccurM.topOccurOfTop : TopOccurOfTopStmt := by sorry
