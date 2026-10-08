-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_triangle_stationary_abs
-- name    : OAI.TwoPointCorrelations.halasz_triangle_stationary_abs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:51.00862+00:00
-- url     : https://prove2.me/theorems/bf82d23b-0263-4d15-8b46-66ed7b9a47bf
-- title:
--   Stationary-phase bound for the triangle-weighted log-phase integral
-- statement:
--   For all reals $N>0$, $u\ne0$ and $v$,
--
--   $$\big|\texttt{halaszTriangleIntegral}\ N\ u\ v\big|\le\frac{110N}{\sqrt{|u|}},$$
--
--   where `halaszTriangleIntegral N u v` $=\int_{N/2}^{3N/2}(\tfrac2Nx-1)\,\phi_{u,v}(x)\,dx+\int_{3N/2}^{5N/2}(5-\tfrac2Nx)\,\phi_{u,v}(x)\,dx$ with the bundle's phase $\phi_{u,v}$ = `halaszLogPhase u v`.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_triangle_stationary_abs`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open MeasureTheory
open Complex
open scoped ComplexConjugate

theorem halasz_triangle_stationary_abs (N u v : ℝ) (hN : 0 < N) (hu : u ≠ 0) :
    ‖halaszTriangleIntegral N u v‖ ≤ 110*N/Real.sqrt |u| := by
  sorry

end OAI.TwoPointCorrelations
