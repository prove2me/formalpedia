-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i1_hasSum_two_geometric
-- name    : FourierJacobi.Analysis.i1_hasSum_two_geometric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:21:58.648871+00:00
-- url     : https://prove2.me/theorems/a4b6a30e-ca27-5a60-a54c-bec9fa55b3e6
-- title:
--   Analysis: i1 has Sum two geometric
-- statement:
--   The Analysis construction uses the i1 has Sum two geometric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L48-L59
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L48-L59

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

theorem FourierJacobi.Analysis.i1_hasSum_two_geometric (C a b : ℂ)
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    HasSum (fun n : ℕ × ℕ => C * a ^ n.1 * b ^ n.2)
      (C * (1 - a)⁻¹ * (1 - b)⁻¹) := by sorry
