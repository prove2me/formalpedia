-- Prove2me | Theorems.Thm_Kyprianou_Ch01_generalFrullaniImproper
-- name    : Kyprianou.Ch01.generalFrullaniImproper
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T08:19:06.494578+00:00
-- url     : https://prove2.me/theorems/a226e972-3054-4c6b-956b-a97a3cbd56c1
-- title:
--   Exercise 1.3(i): general real Frullani improper integral identity
-- statement:
--   Kyprianou (2006), Exercise 1.3(i). For a continuously differentiable real function with a finite limit at +∞, prove the general Frullani identity as the limit of truncated improper integrals ∫₀∞[f(ax)−f(bx)]/x dx=(f(0)−f(∞))log(b/a), for 0<a<b. The formulation uses an improper-limit integral because absolute Lebesgue integrability need not follow from the hypotheses. This is the general analytic input for Lemma 1.7, and is not assumed as a premise.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.3(i), printed p. 27.

import Mathlib
open MeasureTheory Filter Set Real
open scoped Topology
set_option autoImplicit false

theorem Kyprianou.Ch01.generalFrullaniImproper
    (f f' : ℝ → ℝ) (fInfinity : ℝ)
    (hfderiv : ∀ x : ℝ, HasDerivAt f (f' x) x)
    (hfprime : Continuous f')
    (hlimit : Tendsto f atTop (nhds fInfinity))
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Tendsto
      (fun R : ℝ =>
        ∫ x in (1 / R)..R,
          (f (a * x) - f (b * x)) / x)
      atTop
      (nhds ((f 0 - fInfinity) * Real.log (b / a))) := by
  sorry
