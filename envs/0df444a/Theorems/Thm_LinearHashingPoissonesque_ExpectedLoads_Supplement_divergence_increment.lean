-- Prove2me | Theorems.Thm_LinearHashingPoissonesque_ExpectedLoads_Supplement_divergence_increment
-- name    : LinearHashingPoissonesque.ExpectedLoads.Supplement.divergence_increment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:05:01.107196+00:00
-- url     : https://prove2.me/theorems/6e9a0a2f-9340-40ef-bd45-4c2baaac9477
-- title:
--   Proposition 1 (used in the proofs of Theorems 2 and 10) — divergence increment
-- statement:
--   Let $\mu>0$ and $0<s<t$ be real numbers, and write $D(v,\mu)=v\log(v/\mu)-v+\mu$. Then
--
--   $$D(t,\mu)-D(s,\mu)=\int_s^t\log(x/\mu)\,dx\ \ge (t-s)\log(s/\mu).$$
--
--   Both the integral identity and its lower bound are asserted. This estimate controls increments of the Poisson divergence in the maximum-load comparison and dense-threshold estimates.
--
--   Differences from the source:
--   - encoding: the chained integral identity and inequality → a conjunction of the identity with the interval-integral lower bound; reason: both source clauses are retained; continuity of log(x/mu) on the positive interval implies integrability
-- source:
--   Vinayak Kumar, STOC 2027 submission #1155 (October 2026), p.8, Proposition 1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1155.pdf#page=8

import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_PoissonDivergence

namespace LinearHashingPoissonesque.ExpectedLoads.Supplement

/-- Proposition 1, p.8: both the integral identity and its lower bound. -/
theorem divergence_increment (mu s t : ℝ) (hmu : 0 < mu) (hs : 0 < s) (hst : s < t) :
    poissonDivergence t mu - poissonDivergence s mu =
      (∫ x in s..t, Real.log (x / mu)) ∧
    (t - s) * Real.log (s / mu) ≤ (∫ x in s..t, Real.log (x / mu)) := by sorry

end LinearHashingPoissonesque.ExpectedLoads.Supplement
