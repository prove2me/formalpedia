-- Prove2me | Theorems.Thm_GeneralPieces_Remarks_read_as_three
-- name    : GeneralPieces.Remarks.read_as_three
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:00:42.185927+00:00
-- url     : https://prove2.me/theorems/a6cf57be-abf4-465e-8bb5-6ebcbee726ff
-- title:
--   Remarks: read as three
-- statement:
--   «… and a formula with k ≤ 2 is read as a 3-CNF.»
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/Remarks.lean#L80-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/Remarks.lean#L80-L81

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppRunningTimeStatement
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_GeneralPieces_Rec_Rate
import Definitions.Def_GeneralPieces_Num_Remarks
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Remarks
open Finset Levels.Gen ClauseBound.Gen AppRunningTime

theorem GeneralPieces.Remarks.read_as_three {k n : ℕ} (φ : Sat3.CNF n) (hk : k ≤ 3) (h : SatK.IsKCNF k φ) : SatK.IsKCNF 3 φ := by sorry
