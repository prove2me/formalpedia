-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_inverseSqrt_even_zpow
-- name    : FourierJacobi.Analysis.inverseSqrt_even_zpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:35:19.101188+00:00
-- url     : https://prove2.me/theorems/fdffe532-5727-403f-bbf1-059b79cd8fd0
-- title:
--   Analysis: inverse Sqrt even zpow
-- statement:
--   The Analysis construction uses the inverse Sqrt even zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarKernel.lean#L20-L23
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarKernel.lean#L20-L23

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

theorem FourierJacobi.Analysis.inverseSqrt_even_zpow (q : ℝ) (hq : 0 ≤ q) (e : ℤ) :
    inverseSqrt q ^ (2 * e) = q ^ (-e) := by sorry
