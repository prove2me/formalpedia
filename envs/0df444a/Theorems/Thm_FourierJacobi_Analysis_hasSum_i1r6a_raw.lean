-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_hasSum_i1r6a_raw
-- name    : FourierJacobi.Analysis.hasSum_i1r6a_raw
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:01:39.143882+00:00
-- url     : https://prove2.me/theorems/009474c7-06b6-4518-af7c-f943b05f4028
-- title:
--   Analysis: has Sum i1r6a raw
-- statement:
--   The Analysis construction uses the has Sum i1r6a raw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L786-L795
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L786-L795

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Definitions.Def_FourierJacobi_Analysis_I1Complete
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

theorem FourierJacobi.Analysis.hasSum_i1r6a_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖t ^ 2‖ < 1)
    (h1 : ‖t ^ 2‖ < 1) :
    HasSum (fun p : I1R6ARow => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * (T * V) * t^2) * (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) := by sorry
