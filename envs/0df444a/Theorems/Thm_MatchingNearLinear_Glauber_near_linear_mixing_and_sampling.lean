-- Prove2me | Theorems.Thm_MatchingNearLinear_Glauber_near_linear_mixing_and_sampling
-- name    : MatchingNearLinear.Glauber.near_linear_mixing_and_sampling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T15:57:58.084181+00:00
-- url     : https://prove2.me/theorems/3a442f5b-a8a6-4a94-8d7b-79b6ea60a477
-- title:
--   Theorem 1.1 — Near-linear mixing and sampling
-- statement:
--   For each fixed $a>0$ there are constants $c_a>0$ and an integer multiplier $K_a\ge1$, before any graph, activity or accuracy parameter is chosen. For every finite simple graph with $n$ vertices and $m\ge1$ edges, real activities $0<\lambda_e\le a$, and $0<\varepsilon\le1/2$, the original single-edge heat-bath chain satisfies
--
--   $$t_{\rm mix}(\varepsilon)\le c_a m\log^2(n/\varepsilon).$$
--
--   Starting empty, the metered mate-array program with $T=K_amL(n/\varepsilon)^2$ produces a matching on every tape, its actual output law $\widehat p$ is a probability distribution, and
--
--   $$d_{\rm TV}(\widehat p,\mu_{G,\lambda})\le\varepsilon,\qquad \text{work}\le c_a[n+m\log^2(n/\varepsilon)].$$
--
--   For each fixed uniform activity $a>0$ there are parameter-only constants giving, on every such graph,
--
--   $$t_{\rm mix}(\varepsilon)\le c_a m[\log^2n+\log(1/\varepsilon)],\qquad \text{work}\le c_a[n+m(\log^2n+\log(1/\varepsilon))].$$
--
--   The uniform sampler runs $T=K_am(L(n)^2+L(1/\varepsilon))$ original-chain updates, has total-variation error at most $\varepsilon$, and outputs a matching on every tape. Here $L(x)$ is the first doubling exponent with $x\le2^{L(x)}$, computed by an operationally certified loop; schedule computation is charged. Work counts exact random-choice RAM operations, and variable-length input decoding is charged additionally. There is no degree, connectivity, minimum-activity or starting-state promise. All four goal clauses concern the actual matching law and chain.
--
--   Differences from the source:
--   - encoding: finite simple graphs with labeled edge lists → vertices Fin n and edges Fin m with distinct endpoints and injective unordered endpoint map; reason: every finite source graph admits this encoding, including isolated vertices and disconnected graphs
--   - encoding: least nonnegative integer worst-start mixing time bounded by B → existence of a natural horizon t with t ≤ B and total-variation error at most epsilon from every starting state; reason: this is equivalent to the least-time bound and certifies a nonempty set of mixing times
--   - encoding: parameter-uniform or universal big-O bounds → a positive existential constant before all instance parameters; secondary asymptotic clauses quantify fixed bounds first; reason: this is the precise uniform meaning of the source asymptotic notation
--   - encoding: random-choice RAM implementation using a mate array and a sufficiently large fixed horizon → a metered mate-array program, independent exact uniform/Bernoulli tapes and their execution push-forward, with doubling schedules and a parameter-only natural multiplier; reason: trace lengths charge executed primitives; finite-fuel evaluation certifies the oracle-free doubling loop through its independent operational semantics
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), Theorem 1.1, printed p. 1 (PDF p. 3); continues on printed p.2 (PDF p.4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib
import Definitions.Def_MatchingNearLinear_Glauber_Sampler

set_option autoImplicit false

namespace MatchingNearLinear.Glauber

/-- Tianshun Miao and Yitong Yin, Sampling Matchings in Near-linear Time,
STOC 2027 submission #444 (October 2026). Exact result and pages in the item metadata. -/

theorem near_linear_mixing_and_sampling :
    (∀ a : ℝ, 0 < a → ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, 0 < K ∧
      ∀ (n m : ℕ), 1 ≤ m → ∀ (G : Input n m) (lam : Fin m → ℝ),
      ActivityBound lam a → ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 →
      let p := matchingLaw G lam
      let schedule := nonuniformSchedule K m n ε
      MixingBound (supportMass p) (subsetGlauber p) ε (c*m*(Real.log ((n:ℝ)/ε))^2) ∧
      DoublingExecution ((n:ℝ)/ε) 1 0 (computeLength ((n:ℝ)/ε)) ∧
      MarkovMixing.IsDist (outputLaw G lam schedule.1) ∧
      totalVariation (outputLaw G lam schedule.1) p ≤ ε ∧
      (∀ tape, EdmondsMatching65.Polyhedron.IsMatching G.graph (execute G lam schedule.1 tape).1 ∧
        (samplingWork G lam schedule tape : ℝ) ≤ c*((n:ℝ)+m*(Real.log ((n:ℝ)/ε))^2))) ∧
    (∀ a : ℝ, 0 < a → ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, 0 < K ∧
      ∀ (n m : ℕ), 1 ≤ m → ∀ G : Input n m, ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 →
      let lam := fun _ : Fin m => a
      let p := matchingLaw G lam
      let schedule := uniformSchedule K m n ε
      MixingBound (supportMass p) (subsetGlauber p) ε (c*m*((Real.log n)^2+Real.log (1/ε))) ∧
      DoublingExecution (n:ℝ) 1 0 (computeLength (n:ℝ)) ∧
      DoublingExecution (1/ε) 1 0 (computeLength (1/ε)) ∧
      MarkovMixing.IsDist (outputLaw G lam schedule.1) ∧
      totalVariation (outputLaw G lam schedule.1) p ≤ ε ∧
      (∀ tape, EdmondsMatching65.Polyhedron.IsMatching G.graph (execute G lam schedule.1 tape).1 ∧
        (samplingWork G lam schedule tape : ℝ) ≤ c*((n:ℝ)+m*((Real.log n)^2+Real.log (1/ε))))) := by sorry

end MatchingNearLinear.Glauber
