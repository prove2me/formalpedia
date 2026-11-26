-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_coreLocalAbs_pos
-- name    : FourierJacobi.Analysis.coreLocalAbs_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:42:55.149353+00:00
-- url     : https://prove2.me/theorems/b44b5fc3-b137-456c-bd06-ecb3efac903b
-- title:
--   Analysis: core Local Abs pos
-- statement:
--   The Analysis construction uses the core Local Abs pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarKernel.lean#L40-L41
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarKernel.lean#L40-L41

import Definitions.Def_FourierJacobi_Analysis_ExplicitKernel
import Definitions.Def_FourierJacobi_Measure_PaperMultiplicativeHaar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_FourierJacobi_Analysis_HaarKernel
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem FourierJacobi.Analysis.coreLocalAbs_pos (q : ℝ) (hq : 0 < q) (a : Kˣ) :
    0 < coreLocalAbs K q a := by sorry
