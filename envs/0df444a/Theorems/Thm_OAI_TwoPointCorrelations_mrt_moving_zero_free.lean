-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_mrt_moving_zero_free
-- name    : OAI.TwoPointCorrelations.mrt_moving_zero_free
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:14:11.19481+00:00
-- url     : https://prove2.me/theorems/8f8106b6-2a35-460b-a163-392e18c86579
-- title:
--   A zero-free disc argument via bounds for χ and χ² on moving discs
-- statement:
--   There are $c>0$ and $r_0>0$ such that for every natural $q\ne0$, every Dirichlet character $\chi$ modulo $q$, and reals $r,t,B,\beta$ with $0<r\le r_0$, $3r<|t|$ and $B\ge1$: if $|\Lambda_{\chi,r,t}(z)|\le e^B$ and $|\Lambda_{\chi^2,r,2t}(z)|\le e^B$ for all $|z|\le15/16$, where $\Lambda_{\chi,r,t}(z)=L(m_{r,t}(z),\chi)/L(m_{r,t}(0),\chi)$ (`mrtMovingLFunction χ r t`, with the bundle's moving centre map `mrtMovingPoint r t`), and $\beta\ge1-cr/B$, then
--
--   $$L(\beta+it,\chi)\ne0.$$
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.mrt_moving_zero_free`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Complex
open scoped Classical

theorem mrt_moving_zero_free : ∃ c r₀ : ℝ, 0 < c ∧ 0 < r₀ ∧
    ∀ (q : ℕ) [NeZero q], ∀ (χ : DirichletCharacter ℂ q),
    ∀ (r t B β : ℝ), 0 < r → r ≤ r₀ → 3 * r < |t| → 1 ≤ B →
      (∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16),
        ‖mrtMovingLFunction χ r t z‖ ≤ Real.exp B) →
      (∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16),
        ‖mrtMovingLFunction (χ ^ 2) r (2 * t) z‖ ≤ Real.exp B) →
      1 - c * r / B ≤ β →
        DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * (t : ℂ)) ≠ 0 := by
  sorry

end OAI.TwoPointCorrelations
