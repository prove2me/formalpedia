-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_hasSum_i2_probability_ge_two
-- name    : FourierJacobi.Analysis.hasSum_i2_probability_ge_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:17:01.217958+00:00
-- url     : https://prove2.me/theorems/5d3b8dec-ff62-5f11-abf4-3103f673f73e
-- title:
--   Analysis: has Sum i2 probability ge two
-- statement:
--   The Analysis construction uses the has Sum i2 probability ge two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Assembly.lean#L164-L169
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Assembly.lean#L164-L169

import Definitions.Def_FourierJacobi_Analysis_I2Complete
import Definitions.Def_FourierJacobi_Analysis_I2Predicates
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I2Assembly
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem FourierJacobi.Analysis.hasSum_i2_probability_ge_two (q : ℂ) (hq : ‖q⁻¹‖ < 1) :
    HasSum (fun c : ℕ => if 2 ≤ c then collisionProbability q c else 0)
      (q⁻¹ ^ 2 / (1 - q⁻¹)) := by sorry
