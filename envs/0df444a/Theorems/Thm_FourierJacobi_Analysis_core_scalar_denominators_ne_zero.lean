-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_core_scalar_denominators_ne_zero
-- name    : FourierJacobi.Analysis.core_scalar_denominators_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:48:11.150039+00:00
-- url     : https://prove2.me/theorems/2f7316de-45be-4415-8d19-b7ad4264f525
-- title:
--   Analysis: core scalar denominators ne zero
-- statement:
--   The elementary scalar denominators in the displayed paper formula and
--   its principal/special prefactors follow from the natural parameter domain.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLimits.lean#L16-L27
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLimits.lean#L16-L27

import Definitions.Def_FourierJacobi_Analysis_HaarCoreAssembly
import Definitions.Def_FourierJacobi_Analysis_HaarLimits
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations FourierJacobi.Measure
open MeasureTheory Filter
open scoped Topology

theorem FourierJacobi.Analysis.core_scalar_denominators_ne_zero (q : ℝ) (a b : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    (q : ℂ) ≠ 0 ∧ (q : ℂ) + 1 ≠ 0 ∧ (q : ℂ) - 1 ≠ 0 ∧
      (q : ℂ) - 2 ≠ 0 ∧ a * b ≠ 0 := by sorry
