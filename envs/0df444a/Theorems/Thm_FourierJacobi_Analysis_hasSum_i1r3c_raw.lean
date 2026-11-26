-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_hasSum_i1r3c_raw
-- name    : FourierJacobi.Analysis.hasSum_i1r3c_raw
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:00:54.45309+00:00
-- url     : https://prove2.me/theorems/f9083abb-bf6c-532a-ad43-b5ce5326dc06
-- title:
--   Analysis: has Sum i1r3c raw
-- statement:
--   The Analysis construction uses the has Sum i1r3c raw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L539-L548
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L539-L548

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

theorem FourierJacobi.Analysis.hasSum_i1r3c_raw (t d U V T : ℂ) (ht : t ≠ 0) (depth : ℕ) (hdepth : 1 ≤ depth)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    HasSum (fun p : I1R3CRow => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * d * (T * V)^2 / t) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹) := by sorry
