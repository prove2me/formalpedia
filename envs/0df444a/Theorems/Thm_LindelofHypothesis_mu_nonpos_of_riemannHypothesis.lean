-- Prove2me | Theorems.Thm_LindelofHypothesis_mu_nonpos_of_riemannHypothesis
-- name    : LindelofHypothesis.mu_nonpos_of_riemannHypothesis
-- status  : Proved
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:19:47.538128+00:00
-- url     : https://prove2.me/theorems/b94a9049-7baa-43a4-844f-3a4a8b26cca7
-- title:
--   Under RH, the growth exponent of zeta is at most 0 to the right of the critical line
-- statement:
--   Assume the Riemann hypothesis. Then for every real sigma > 1/2 the growth exponent satisfies mu(sigma) <= 0, i.e. zeta(sigma + iT) = O(T^epsilon) as T -> +infinity for every epsilon > 0. (Since mu(sigma) = 0 for sigma > 1 is already a milestone, the content is the strip 1/2 < sigma <= 1.) Source: Titchmarsh, The Theory of the Riemann Zeta-Function, 2nd ed., Section 14.2 (zeta(s) = O(t^epsilon) for sigma >= 1/2 + delta under RH, via Borel-Caratheodory on log zeta). Formalization note: mu is LindelofHypothesis.mu, valued in the extended reals; RiemannHypothesis is Mathlib's. This is the analytic core of the milestone 'the Riemann hypothesis implies the Lindelof hypothesis'; the passage from here to sigma = 1/2 is by convexity of mu and is carried out in the reduction.
-- source:
--   https://en.wikipedia.org/wiki/Lindel%C3%B6f_hypothesis

import Mathlib
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

namespace LindelofHypothesis

theorem mu_nonpos_of_riemannHypothesis (hRH : RiemannHypothesis) (σ : ℝ) (hσ : 1 / 2 < σ) :
    mu σ ≤ 0 := by sorry

end LindelofHypothesis
