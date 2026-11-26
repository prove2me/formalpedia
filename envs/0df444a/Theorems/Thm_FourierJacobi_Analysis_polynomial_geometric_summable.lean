-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_polynomial_geometric_summable
-- name    : FourierJacobi.Analysis.polynomial_geometric_summable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:38:44.886852+00:00
-- url     : https://prove2.me/theorems/333f3bb9-e035-40f5-a518-b04be116b857
-- title:
--   Analysis: polynomial geometric summable
-- statement:
--   The Analysis construction uses the polynomial geometric summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/Damping.lean#L20-L23
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/Damping.lean#L20-L23

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_FourierJacobi_Analysis_Damping
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Analysis
open MeasureTheory Filter
open scoped Topology

theorem FourierJacobi.Analysis.polynomial_geometric_summable (k : ℕ) {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    Summable (fun n : ℕ => (n : ℝ) ^ k * r ^ n) := by sorry
