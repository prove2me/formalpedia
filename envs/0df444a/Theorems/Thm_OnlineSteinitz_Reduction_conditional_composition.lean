-- Prove2me | Theorems.Thm_OnlineSteinitz_Reduction_conditional_composition
-- name    : OnlineSteinitz.Reduction.conditional_composition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:34.05837+00:00
-- url     : https://prove2.me/theorems/ccfdf006-e475-43af-9939-fa07348ea567
-- title:
--   Lemma 2.4 — conditional composition
-- statement:
--   There is an absolute constant $C>0$, uniform over all positive dimensions, horizons, eligible signer families, common scales $\Sigma\ge1$ and fixed Euclidean unit-ball inputs, with the following property. Write $h=\lceil\log_2T\rceil$ and use the actual local $Y_u,q_u$ of Algorithm 1. For every $0\le k\le T$ and every $s>0$,
--   $$\mathbb P\left(\left\|\frac12\sum_{u\in P(k)}\alpha_{u,k}Y_u\right\|_2>C\Sigma\sqrt{h(d+s)}\right)\le e^{-s},$$
--   $$\mathbb P\left(\sum_{u\in P(k)}\alpha_{u,k}|q_u|>C\Sigma\sqrt{h(h+s)}\right)\le e^{-s}.$$
--   Both strict-exceedance tail bounds use the same absolute constant. The hypotheses are only the fixed-stream terminal MGF bounds, measurable online decisions and independent private tapes. This statement combines path terms even when ancestor routing makes node errors dependent.
--
--   Differences from the source:
--   - encoding: positions and arrivals indexed from 1 → zero-based slots and arrivals, with half-open intervals [a,a+m); reason: subtracting one from indices preserves every input and prefix, including k=0,T; values outside the first T slots are ignored
--   - encoding: persistent signer state updated with proposed signs and supplied routing statistics → a tape-dependent function of the current vector and the local vector/proposed-sign history; reason: the capacity is known and quota repair reconstructs all child counts, sums and remaining capacities from this history; state can be replayed without consulting future vectors or descendant tapes
--   - encoding: independent private tapes at the internal nodes → a finite product probability law on an interval grid, with arbitrary measurable tape carrier and node-specific marginal laws; reason: unused coordinates are dummy independent tapes; the router reads only visited nodes, while ancestor conditioning retains the complete tapes
--   - encoding: real probability comparisons → extended nonnegative measure values and ENNReal.ofReal on the real comparison bound; reason: probabilities are finite under the product probability law; a negative lower bound becomes the equivalent tautological lower bound zero
-- source:
--   Russo–Wei, The Online Steinitz Problem, STOC 2027 submission #22 (2026 preprint), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/22.pdf, SHA-256 32ff14f15a94c95630765c77f4fa5a429fb294bcf03a9055ed67c60658769366, Lemma 2.4, p.10, equations (2.11)–(2.12)

import Definitions.Def_OnlineSteinitz_Reduction_Randomness

open MeasureTheory

namespace OnlineSteinitz.Reduction

/-- Lemma 2.4, p.10, both (2.11) and (2.12). The absolute constant precedes
every instance parameter. There is no independence assumption on node errors. -/
theorem conditional_composition : ∃ C : ℝ, 0 < C ∧
    ∀ (T d : ℕ), 0 < T → 0 < d →
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Node T → Measure Ω)
      [∀ u, IsProbabilityMeasure (μ u)] (r : Node T → Signer (Vec (d + 1)) Ω),
    (∀ u ∈ internalNodes T, MeasurableSigner (r u)) →
    ∀ sigma : ℝ, 1 ≤ sigma →
    (∀ u ∈ internalNodes T, HasScale (μ u) u.2.val (r u) sigma) →
    ∀ v : Fin T → Vec d, (∀ i, ‖v i‖ ≤ 1) →
    ∀ k : ℕ, k ≤ T → ∀ s : ℝ, 0 < s →
      (tapeLaw μ) {ω | ‖centeredPath (euclideanRun r v ω) k‖ >
        C * sigma * Real.sqrt ((height T : ℝ) * (d + s))} ≤ ENNReal.ofReal (Real.exp (-s)) ∧
      (tapeLaw μ) {ω | countPath (euclideanRun r v ω) k >
        C * sigma * Real.sqrt ((height T : ℝ) * (height T + s))} ≤
          ENNReal.ofReal (Real.exp (-s)) := by sorry

end OnlineSteinitz.Reduction
