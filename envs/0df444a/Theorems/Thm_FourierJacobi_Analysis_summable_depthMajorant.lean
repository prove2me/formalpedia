-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_summable_depthMajorant
-- name    : FourierJacobi.Analysis.summable_depthMajorant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:24:30.462187+00:00
-- url     : https://prove2.me/theorems/5994ef97-8786-40ce-9dcb-b2b27a9a4a52
-- title:
--   Analysis: summable depth Majorant
-- statement:
--   The Analysis construction uses the summable depth Majorant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/MasterSeries.lean#L138-L141
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/MasterSeries.lean#L138-L141

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Analysis_MasterSeries
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations

theorem FourierJacobi.Analysis.summable_depthMajorant (q : ℂ) (hq : ‖q⁻¹‖ < 1) :
    Summable (depthMajorant q) := by sorry
