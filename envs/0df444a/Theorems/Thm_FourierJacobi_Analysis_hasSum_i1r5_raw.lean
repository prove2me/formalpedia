-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_hasSum_i1r5_raw
-- name    : FourierJacobi.Analysis.hasSum_i1r5_raw
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:01:20.728806+00:00
-- url     : https://prove2.me/theorems/c74559f2-a9ad-4557-90a0-5e48516856b5
-- title:
--   Analysis: has Sum i1r5 raw
-- statement:
--   The Analysis construction uses the has Sum i1r5 raw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L703-L713
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L703-L713

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

theorem FourierJacobi.Analysis.hasSum_i1r5_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖T * U * t ^ 2‖ < 1)
    (h2 : ‖T * U * t ^ 4‖ < 1) :
    HasSum (fun p : I1R5Row => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^5) * (1 - d * T * V * t)⁻¹ * (1 - T * U * t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹) := by sorry
