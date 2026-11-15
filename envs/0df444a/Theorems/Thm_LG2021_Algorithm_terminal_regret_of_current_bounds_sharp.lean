-- Prove2me | Theorems.Thm_LG2021_Algorithm_terminal_regret_of_current_bounds_sharp
-- name    : LG2021.Algorithm.terminal_regret_of_current_bounds_sharp
-- status  : Proved
-- author  : @sim2000dg
-- created : 2026-11-14T16:28:16.687197+00:00
-- url     : https://prove2.me/theorems/875008e3-6a0b-4738-8762-6a771e3f8f34
-- title:
--   Deterministic sharp regret closure for the ellipsoid bandit policy
-- statement:
--   Fix a seed and paired-observation path of the concrete ellipsoid bandit policy. Let $L$ be the explicit logarithmic parameter, let $\kappa=4096d\sqrt d$, and let $q$ be its sample budget. Under the stated scalar and winner-local gradient confidence bounds, candidate coverage, source near-minimizer simplex conditions, volume-stage inequality, and path-loss comparison, every path-loss quantity $r$ satisfying those hypotheses obeys
--   $$r\le2\sqrt{4\kappa^2q+1}\sqrt{129nd^2L}+\sqrt{n\log n}+4(\kappa+1)+1.$$
--   The exact budget, trace, confidence radii, and simplex volume are those of the public policy definitions.
--
--   This deterministic implication preserves the source simplex through the cuts, controls the number of volume stages, and sums the effective gaps over those stages. The confidence hypotheses are established separately by the adaptive confidence theorems; the implication itself makes no probability assertion. It is the deterministic component used to obtain the original explicit dimension-dependent statistical bound.
-- source:
--   Tor Lattimore and András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, Proceedings of the 34th Conference on Learning Theory (COLT 2021), Proceedings of Machine Learning Research 134:2938–2964, 2021, Algorithm 2 and Section 7, with the analysis simplex of Lemma 7. Deterministic stage and regret derivation for the formalized policy.

import Mathlib
import Definitions.Def_LG2021_Policy
import Definitions.Def_LG2021_RegretRate
open LG2021 LG2021.Algorithm LG2021.Concentration MeasureTheory Set

theorem LG2021.Algorithm.terminal_regret_of_current_bounds_sharp {d n N : ℕ} (hd : 0 < d) (hn : 2 ≤ n)
    {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K)
    {R D : ℝ} (hR : 0 < R) (hRD : R ≤ D)
    (hbounded : ∀ x ∈ K, ‖x‖ ≤ R) (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (seed : Seed d (candidateCount n) n) (ys : ℕ → ℝ × ℝ)
    (f : Space d → ℝ) (hf : LipschitzWith 1 f) (hc : ConvexOn ℝ univ f)
    (xstar : Space d) (hmin : ∀ x ∈ K, f xstar ≤ f x)
    (v : Fin (d + 1) → Space d) (hv0 : v 0 = xstar) (hv : ∀ i, v i ∈ K)
    (hnear : ∀ i, f (v i) ≤ f xstar + Real.exp (-parameterLog d D n))
    (hvol : ENNReal.ofReal (sourceSimplexVolume d D (parameterLog d D n)) ≤
      volume (convexHull ℝ (range v))) (hN : N ≤ n) {r : ℝ}
    (hseed : ∀ p ≤ N, ∀ s, ‖seedCandidates seed p s‖ ≤
      (oracleConfig d D n).radius / (2 * (d : ℝ)))
    (hscalar : ∀ p < N,
      (interior (codedBody K (traceState (oracleConfig d D n) K R seed ys p).1)).Nonempty →
      ∀ s, |traceScalar (oracleConfig d D n) K R seed ys p s -
        traceGap (oracleConfig d D n) K R seed ys f p s| ≤
          confidenceRadius (oracleConfig d D n) (candidateCount n)
            (traceSampleCount (oracleConfig d D n) K R seed ys p))
    (hgradient : ∀ p < N,
      (interior (codedBody K (traceState (oracleConfig d D n) K R seed ys p).1)).Nonempty →
      (∀ i, v i ∈ codedBody K (traceState (oracleConfig d D n) K R seed ys p).1) →
      ∀ s, traceWinner (oracleConfig d D n) K R seed ys p = some s →
      ∀ i, traceGradientDeviation (oracleConfig d D n) K R seed ys f p s (v i) ≤
        2 * (oracleConfig d D n).radius *
          ((oracleConfig d D n).momentConstant * Real.sqrt
            (confidenceLog (oracleConfig d D n) (candidateCount n) /
              ((oracleConfig d D n).concentrationConstant *
                (traceSampleCount (oracleConfig d D n) K R seed ys p : ℝ))) +
            1 / (8 * (oracleConfig d D n).radius * n)))
    (hhit : (∀ p ≤ N,
      (interior (codedBody K (traceState (oracleConfig d D n) K R seed ys p).1)).Nonempty) →
      (∀ p ≤ N, xstar ∈ codedBody K (traceState (oracleConfig d D n) K R seed ys p).1) →
      ∀ p ≤ N, ∃ s : Fin (candidateCount n),
        (traceComparatorGap (oracleConfig d D n) K R seed ys f xstar p - 1 / (n : ℝ)) /
          separationFactor d ≤ traceGap (oracleConfig d D n) K R seed ys f p s)
    (hpath : (∀ p < N,
      (interior (codedBody K (traceState (oracleConfig d D n) K R seed ys p).1)).Nonempty) →
      r ≤ 2 * (∑ p ∈ Finset.range N,
        min 1 (traceComparatorGap (oracleConfig d D n) K R seed ys f xstar p)) +
          Real.sqrt ((n : ℝ) * Real.log n) + 1) :
    (8 * ((d : ℝ) + 1) * ((d : ℝ) * Real.log R -
      Real.log (sourceSimplexVolume d D (parameterLog d D n) / (2 : ℝ)^d)) ≤
        128 * (d : ℝ)^2 * parameterLog d D n) →
    r ≤ sharpPathBound d D n := by sorry
