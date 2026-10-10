-- Prove2me | Theorems.Thm_HunterPDE_Newtonian_tendsto_weighted_ball_integral_zero
-- name    : HunterPDE.Newtonian.tendsto_weighted_ball_integral_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T20:53:19.523714+00:00
-- url     : https://prove2.me/theorems/77b6817c-b9f6-4207-b2ef-18489c578afc
-- title:
--   Vanishing Newtonian boundary coefficient for bounded ball data
-- statement:
--   Let $n\ge2$, let $v\in\mathbb R^n$ be a unit vector, and let $g:\mathbb R^n\to\mathbb R$ satisfy $|g(y)|\le C$ everywhere. For every $x\in\mathbb R^n$,
--
--   $$\lim_{r\downarrow0}\Gamma_n(rv)\int_{B_r(x)}g(y)\,dy=0.$$
--
--   This is the vanishing first boundary contribution in the ball-integral form of Green's representation. It applies to any bounded data, independently of differentiability and compact support.
--
--   **Formalization Note.** The integral is Lean's total Bochner integral. Measurability is not assumed: for nonintegrable data it is zero by convention, while for integrable data the assertion is the usual Lebesgue integral limit.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, printed pp. 33, 35–36, Eq. (2.12), (2.20)–(2.21). Generalization of the vanishing boundary flux, after the divergence theorem expresses the flux as a ball integral; volume scaling makes the bound O(r²) for n≥3 and O(r² |log r|) for n=2.

import Definitions.Def_HunterPDE_Newtonian_FundamentalSolution
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory MeasureTheory.Measure Filter Set Topology
open HunterPDE.Newtonian

theorem HunterPDE.Newtonian.tendsto_weighted_ball_integral_zero (n : ℕ) (hn : 2 ≤ n)
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (C : ℝ) (hC : ∀ y, ‖g y‖ ≤ C)
    (x : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun r : ℝ => fundamentalSolution n (r • v) *
      ∫ y in Metric.ball x r, g y) (𝓝[>] 0) (𝓝 0) := by sorry
