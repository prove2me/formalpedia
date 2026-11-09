-- Prove2me | Theorems.Thm_MLAMaxDelay_RandomizedTimer_randomized_competitive
-- name    : MLAMaxDelay.RandomizedTimer.randomized_competitive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:41:28.601442+00:00
-- url     : https://prove2.me/theorems/c8e35cc8-7a80-44ec-ba22-f39257d3f9ec
-- title:
--   Theorem 5.3 — randomized e/(e − 1) competitiveness
-- statement:
--   On every finite rooted tree with nonnegative real edge weights and at least one positive edge, sample one global real parameter $\Theta$ with density $\exp(\theta)/(\exp(1)-1)$ on $[0,1]$. For every finite labelled input $I$, fixed independently of that draw, the actual OPT-Timer execution satisfies
--   $$\mathbb E_{\Theta}\!\left[\operatorname{cost}(\operatorname{OPT\text{-}Timer}(\Theta),I)\right]\le\frac{\exp(1)}{\exp(1)-1}\operatorname{OPT}(I).$$
--   There is no additive term. The statement also requires the defined seed measure to be a probability measure with the stated CDF, and proves causality and feasibility for every fixed $\theta\in[0,1]$, plus measurability of the actual extended cost. Empty inputs, coincident arrivals, zero edges and zero-path-only inputs are included.
--
--   **Formalization Note.** The expectation is a nonnegative extended integral, so infeasible schedules remain infinite and nonintegrability cannot silently yield zero. The seed is reused in every block. The offline benchmark is independently defined over actual rooted service schedules.
--
--   Differences from the source:
--   - encoding: finite undirected rooted tree and nonnegative real edge weights → published rooted parent-map tree with nonroot vertices naming their parent edges; reason: every source tree admits this orientation and every such parent map gives the unique root paths; zero edges and arbitrary finite branching are retained
--   - encoding: finite labelled request occurrences → finite sets of natural-number occurrence labels with arrival and location maps; reason: every finite labelled input admits an injective relabelling; equal times and locations remain distinct
--   - encoding: actual schedule minimum, charges defined on nonempty batches, and infinite infeasible cost → ENNReal infimum over finite useful schedules, empty services charged only spatial weight, with toReal for finite-input algebra; reason: there are at most N useful services; empty services can be removed without benefit and do not affect the minimum; Proposition 3.1 explicitly asserts finite attainment, so no default real infimum or infinite toReal is used
--   - encoding: the named online algorithm and the continuous global law in Section 2 and equation (17) → explicit causality, feasibility, probability normalization, CDF identity and cost measurability conjuncts alongside the competitive inequality; reason: these certify the mathematical meaning of the actual finite event evaluator and extended expectation; none is assumed as a hypothesis
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Multi-Level Aggregation with Maximum Delay, STOC 2027 submission #217 (October 2026), p. 14, Theorem 5.3; proof pp. 14–15; equation (17) p. 13; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/217.pdf

import Definitions.Def_MLAMaxDelay_RandomizedTimer_RandomLaw

namespace MLAMaxDelay.RandomizedTimer

open MeasureTheory

/-- Theorem 5.3, pp. 14–15, with the online/feasibility and probability-law
well-posedness guarantees of §2 and Algorithms 1–2. The input is outside the seed
integral: the adversary is oblivious. No favorable trace or integrability assumed. -/
theorem randomized_competitive {V : Type} [Fintype V] [DecidableEq V]
    (T : WeightedTree V) :
    IsProbabilityMeasure seedLaw ∧
    (∀ x : ℝ, seedLaw (Set.Iic x) = ENNReal.ofReal (seedCDF x)) ∧
    (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → Causal (fun I => optTimer T I θ)) ∧
    (∀ I : Input V,
      (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → Feasible T I (optTimer T I θ)) ∧
      Measurable (fun θ => cost T I (optTimer T I θ)) ∧
      expectedCost T I ≤ ENNReal.ofReal (Real.exp 1 / (Real.exp 1 - 1)) * optimum T I) := by sorry

end MLAMaxDelay.RandomizedTimer
