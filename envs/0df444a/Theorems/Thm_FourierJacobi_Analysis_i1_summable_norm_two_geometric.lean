-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_i1_summable_norm_two_geometric
-- name    : FourierJacobi.Analysis.i1_summable_norm_two_geometric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:21:32.304731+00:00
-- url     : https://prove2.me/theorems/990a11fc-b16b-4577-9518-3440dab2ec35
-- title:
--   Analysis: i1 summable norm two geometric
-- statement:
--   The Analysis construction uses the i1 summable norm two geometric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L42-L46
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean#L42-L46

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

theorem FourierJacobi.Analysis.i1_summable_norm_two_geometric (C a b : ℂ)
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    Summable (fun n : ℕ × ℕ => ‖C * a ^ n.1 * b ^ n.2‖) := by sorry
