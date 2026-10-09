-- Prove2me | Theorems.Thm_Function_Periodic_intervalIntegral_zero_natCast_eq
-- name    : Function.Periodic.intervalIntegral_zero_natCast_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-08T18:41:36.183196+00:00
-- url     : https://prove2.me/theorems/00582b08-8e99-4c94-9a26-dbce46d93a7c
-- title:
--   The integral of a 1-periodic function over [0, k] is k times its integral over one period, without integrability assumptions
-- statement:
--   Let $E$ be a real normed space and $g:\mathbb{R}\to E$ a $1$-periodic function. Then for every natural number $k$,
--   $$\int_0^k g(x)\,dx = k\int_0^1 g(x)\,dx.$$
--   No integrability hypothesis is assumed. Integrals are Bochner interval integrals, which are $0$ for non-integrable functions.
-- source:
--   Elementary. Used to scale the Gauss linking integral under k-fold covers of a loop (HryniewiczCriterion.gaussLinkingIntegral_comp_mul_nat), for U. Hryniewicz, arXiv:1105.2077, Lemma 3.12.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

theorem Function.Periodic.intervalIntegral_zero_natCast_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} (hg : Function.Periodic g 1) (k : ℕ) :
    ∫ x in (0 : ℝ)..(k : ℝ), g x = (k : ℝ) • ∫ x in (0 : ℝ)..1, g x := by sorry
