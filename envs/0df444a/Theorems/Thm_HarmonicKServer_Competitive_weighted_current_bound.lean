-- Prove2me | Theorems.Thm_HarmonicKServer_Competitive_weighted_current_bound
-- name    : HarmonicKServer.Competitive.weighted_current_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:00:07.918802+00:00
-- url     : https://prove2.me/theorems/05ea6101-9b95-40e7-9ec2-bba77bf8b5f2
-- title:
--   Lemma 5.1 — Weighted current bound
-- statement:
--   Let $Y$ be a distinct-location adversary configuration with $k\ge2$, let $q$ be any nonnegative integer occupancy of mass $k$, and fix a label $s$. Every minimizing flow for $q+e_s-(1+1/k)\mathbf1$ satisfies
--   $$\sum_{i\ne s}q_iF_{is}+kq_s\ge\frac1k.$$
--   The $kq_s$ term is retained. These counts arise from an arbitrary assignment, so $q_s$ can be positive even if the actual request at $y_s$ is not covered by the online configuration. This is the full lower bound used for the expected online potential decrease.
--
--   Differences from the source:
--   - encoding: labels [k] with k at least two in Sections 2–5 → Fin k and an explicit 2 ≤ k hypothesis; reason: the finite label change is a bijection; this is the source analysis regime, not a restriction on the headline goal
--   - encoding: nonnegative integer occupancies q of mass k → natural counts with sum k, cast to reals in the excess vector; reason: natural numbers represent exactly the nonnegative integers; no natural subtraction occurs in this statement
-- source:
--   Yichen Huang, STOC 2027 submission #95 (October 2026), p. 11, Lemma 5.1 (PDF p. 12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/95.pdf; pinned PDF SHA256 20635ef9c29593d01fa406f1a63fdc6b98250e5fc1b1b5c4ed088b407a4e8fd6. Title-page date: November 3, 2026; canonical metadata citation: October 2026.

import Definitions.Def_HarmonicKServer_Competitive_Electrical
import Definitions.Def_HarmonicKServer_Competitive_Harmonic

namespace HarmonicKServer.Competitive
open scoped BigOperators ENNReal
open MeasureTheory

/-- Lemma 5.1; the k*q_s term is retained even on uncovered requests. -/
theorem weighted_current_bound {k : ℕ} (hk : 2 ≤ k) {V : Type*} [MetricSpace V]
    (Y : KServer.Config k V) (hY : Function.Injective Y)
    (q : Fin k → ℕ) (hq : Occupancy q) (s : Fin k) (F : Flow k)
    (hF : Minimizing Y (commonExcess q s) F) :
    (∑ i ∈ Finset.univ.filter (fun i => i ≠ s), (q i : ℝ) * F i s) +
      (k : ℝ) * (q s : ℝ) ≥ 1 / (k : ℝ) := by sorry

end HarmonicKServer.Competitive
