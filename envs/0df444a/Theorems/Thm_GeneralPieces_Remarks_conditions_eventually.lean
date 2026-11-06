-- Prove2me | Theorems.Thm_GeneralPieces_Remarks_conditions_eventually
-- name    : GeneralPieces.Remarks.conditions_eventually
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:00:41.297626+00:00
-- url     : https://prove2.me/theorems/d0600c1e-d419-459a-aca1-ccd8f404506b
-- title:
--   Remarks: conditions eventually
-- statement:
--   «… whose conditions n ≥ K₀^17 and k ≤ (log n)^{1/4} hold for all but finitely many n when k is
--   fixed».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/Remarks.lean#L66-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/Remarks.lean#L66-L77

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

theorem GeneralPieces.Remarks.conditions_eventually (k K₀ : ℕ) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → K₀ ^ 17 ≤ n ∧ (k : ℝ) ≤ Real.logb 2 n ^ (1 / 4 : ℝ) := by sorry
