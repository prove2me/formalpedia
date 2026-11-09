-- Prove2me | Theorems.Thm_HarmonicKServer_Competitive_harmonic_competitive
-- name    : HarmonicKServer.Competitive.harmonic_competitive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:01:12.780279+00:00
-- url     : https://prove2.me/theorems/2dd7bacb-5e48-478c-8397-1683786e1e0e
-- title:
--   Theorem 1.1 — Harmonic is $2k^4$-competitive against adaptive online adversaries
-- statement:
--   Let $(V,d)$ be any metric space, let $k\ge1$, and let $X_0,Y_0\in V^k$ be arbitrary labelled initial configurations, allowing collocations. For the fixed Harmonic algorithm of Section 2 there is a finite $B\ge0$, depending only on the metric, $k$ and the two initial configurations, such that every causal adaptive online adversary and every finite horizon $N\ge0$ satisfy
--   $$\mathbb E[C_{\rm Harmonic}(N)]\le2k^4\mathbb E[C_{\rm ADV}(N)]+B.$$
--   The adversary selects and serves each request before the fresh Harmonic sample, and may react to every previous online move. Arbitrary private random seeds and adaptive service schedules are admitted; infinite expected adversary cost is retained as an extended nonnegative value. The additive constant is quantified before seed spaces, seed laws, policies and horizons. No movement property, potential bound, distinct starting positions or finite-metric assumption is a hypothesis.
--
--   The paper proves this result mathematically. This item asks for its Lean proof, including the $k=1$ case and the causal lazification and private-edge reductions from the analysis convention $k\ge2$ with distinct lazy adversary locations.
--
--   Differences from the source:
--   - encoding: multisets of k servers on an arbitrary metric → labelled configurations Fin k → V, with k ≥ 1; reason: labels only distinguish server choices and movement charges; collocations and every original metric remain admissible
--   - encoding: expected costs against arbitrary randomized adaptive online adversaries → arbitrary measurable private-seed mixtures of full completed-label-history policies and nonnegative extended expectations; reason: the complete past is reconstructible from the seed and label prefix, so requests remain adaptive; the explicit interaction and conditioning bridge retain randomized policies and infinite expected costs
-- source:
--   Yichen Huang, STOC 2027 submission #95 (October 2026), p. 1, Theorem 1.1; §2 model, p. 3, and proof §5, p. 12 (PDF p. 2); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/95.pdf; pinned PDF SHA256 20635ef9c29593d01fa406f1a63fdc6b98250e5fc1b1b5c4ed088b407a4e8fd6. Title-page date: November 3, 2026; canonical metadata citation: October 2026.

import Definitions.Def_HarmonicKServer_Competitive_Interaction

namespace HarmonicKServer.Competitive
open scoped BigOperators ENNReal
open MeasureTheory

/-- Theorem 1.1: every metric, k>=1, arbitrary starts, all adaptive online adversaries.
No potential or movement-property hypotheses are assumed. -/
theorem harmonic_competitive {k : ℕ} (hk : 1 ≤ k) {V : Type*} [MetricSpace V]
    (X₀ Y₀ : KServer.Config k V) :
    AdaptiveCompetitive X₀ Y₀ (2 * (k : ℝ)^4) := by sorry

end HarmonicKServer.Competitive
