-- Prove2me | Theorems.Thm_GirthFiltering_RandomFiltering_threshold_tail_bound
-- name    : GirthFiltering.RandomFiltering.threshold_tail_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:53.388944+00:00
-- url     : https://prove2.me/theorems/fdeba94e-ff80-42bf-b5ca-6981756b76f4
-- title:
--   Theorem 3.1 — threshold tail bound (corrected: nonnegative threshold)
-- statement:
--   Let $G$ be a finite undirected graph with $n$ vertices, $m$ labeled edges, and strictly positive real weights. Independently sample $X_e\sim\operatorname{Exp}(\ell(e))$. Let $H_t$ retain precisely those edges with $X_e\ge t$, and let $T$ be its critical cycle threshold. If $G$ has a cycle, its actual weighted girth satisfies $0<g<\infty$, and for every real $t$ the upper bound below holds, while the lower bound holds for every real $t\ge0$:
--
--   $$
--   e^{-tg}\le\Pr[T\ge t]\le2mn(2m+1)e^{-tg}.
--   $$
--
--   For a forest, $T=-\infty$ on every label tape, and its tail at any finite real threshold has probability zero. The probability is taken under the finite product of continuous exponential laws, rather than inferred from marginal distributions alone.
--
--   The result controls the event that any cycle survives; it is the single source-numbered milestone supporting the estimator. The constant $2mn(2m+1)$ and both bounds are retained exactly.
--
--   Differences from the source:
--   - correction: no explicit threshold-domain restriction → the displayed lower bound is required only for t ≥ 0, and the upper bound is kept for every real t; reason: a unit-weight triangle has g = 3 and tail 1 at t = −1, so the unrestricted lower bound would require exp(3) ≤ 1; the upper bound is true at every t
--   - reading: sampling notation in Theorem 3.1 and a minimum cycle in its proof → independent rate-weight exponential labels; cyclic positive finite girth, with forests stated separately; reason: independence is specified in Section 1.1 and used in the proof; positive weights follow Section 1.2; the forest split avoids the undefined product 0 times infinity
--   - encoding: weighted cycles and the critical-threshold supremum → finite labeled cycle incidences, ENNReal girth and EReal maximum of cycle bottlenecks; reason: loops and parallel edges are retained; complete-lattice extrema give forest values without a default real supremum
--   - generalization: the Section 1.2 convention deletes isolated vertices and assumes 2m ≥ n → the tail bound also permits isolated vertices and n > 2m; reason: isolated vertices change neither cycles nor girth; including them only increases the nonnegative upper-bound coefficient through n
-- source:
--   Yablon, Approximating the Girth of an Undirected, Weighted Graph for Larger Approximation Factors, STOC 2027 submission #59 (2026), pinned PDF sha256 cf63df259cbd099089184755e2c32f0d51f00dea322509f35766f4a91a4e021f, p. 5, Theorem 3.1 (proof continues on p. 6); p. 5, Algorithm 2 forest convention; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/59.pdf

import Definitions.Def_GirthFiltering_RandomFiltering_CycleModel
open scoped ENNReal

namespace GirthFiltering.RandomFiltering

/-- Theorem 3.1, PDF p. 5 (proof p. 6), lower bound corrected to t >= 0; the
upper bound is kept for every real t, as printed.
The cyclic positive case uses actual weighted girth; forests have threshold
-infinity deterministically and zero tail at every finite threshold. -/
theorem threshold_tail_bound (G : WeightedGraph)
    (hU : VehicleRoutingSurvey.Routing.Undirected G) (hW : PositiveWeights G) :
    ((¬ HasCycle G) →
      (∀ X : Fin G.q → ℝ,
        criticalThreshold G (fun e => (X e : EReal)) = ⊥) ∧
      ∀ t : ℝ, labelLaw G {X | (t : EReal) ≤
        criticalThreshold G (fun e => (X e : EReal))} = 0) ∧
    (HasCycle G → 0 < girth G ∧ girth G < ⊤ ∧
      ∀ t : ℝ,
        (0 ≤ t → ENNReal.ofReal (Real.exp (-t * (girth G).toReal)) ≤
          labelLaw G {X | (t : EReal) ≤
            criticalThreshold G (fun e => (X e : EReal))}) ∧
        labelLaw G {X | (t : EReal) ≤
            criticalThreshold G (fun e => (X e : EReal))} ≤
          ENNReal.ofReal (2 * (G.q : ℝ) * (G.n : ℝ) * (2 * (G.q : ℝ) + 1) *
            Real.exp (-t * (girth G).toReal))) := by sorry

end GirthFiltering.RandomFiltering
