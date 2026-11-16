-- Prove2me | Theorems.Thm_MLAMaxDelay_RandomizedTimer_Supplement_randomized_lower_bound
-- name    : MLAMaxDelay.RandomizedTimer.Supplement.randomized_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:58:12.700891+00:00
-- url     : https://prove2.me/theorems/fc06191f-f993-483c-87d5-37144d686195
-- title:
--   Theorem A.4 — no randomized online algorithm beats ratio e/(e−1)
-- statement:
--   Let $T$ be any weighted rooted tree (one-leaf trees included). A randomized online algorithm is a probability space $(\Omega,\mu)$ of random seeds together with a deterministic online algorithm $\mathcal A_\omega$ for each seed, the cost on each input being measurable in the seed. For every such algorithm and every $\gamma<e/(e-1)$ there is an input $I$, fixed independently of the seed, with
--
--   $$\mathbb E_\omega[\mathrm{ALG}_{\mathcal A_\omega}(I)]>\gamma\,\mathrm{OPT}(I).$$
--
--   Thus no randomized online algorithm against an oblivious adversary has competitive ratio below $e/(e-1)$, and the goal Theorem 5.3 is optimal.
--
--   Differences from the source:
--   - encoding: finite rooted tree with nonnegative edge weights and at least one positive edge (Section 2 standing assumption) → the published WeightedTree (parent map, nonnegative non-root weights, a positive edge); reason: the base mission's moderated model; every source tree is represented
--   - encoding: finite labelled request occurrences → a Finset of natural-number labels with arrival and location maps (published Input); reason: every finite labelled input admits an injective relabelling; simultaneous arrivals and repeated locations are kept
--   - encoding: costs in ℝ with +∞ for an infeasible schedule; OPT the minimum over feasible offline schedules → ℝ≥0∞ costs, ⊤ for infeasible, OPT the infimum over all finite schedules (published cost and optimum); reason: the same values; attainment is part of the base milestones
--   - encoding: a randomized online algorithm with expected cost E[ALG(I)] over internal randomness → an arbitrary probability space of seeds, a causal algorithm per seed, and measurability of ω ↦ cost for each input; E is the lower Lebesgue integral; reason: measurability is what makes E[ALG(I)] defined in Section 2; seeds are not restricted to [0,1] or to finite spaces
--   - encoding: no competitive ratio below e/(e−1), even if the tree has only one leaf → for every real γ < e/(e−1), ∃ I with ofReal γ · optimum < ∫⁻ cost; every tree is allowed; reason: the input is chosen after the algorithm and outside the integral (oblivious adversary)
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Multi-Level Aggregation with Maximum Delay, STOC 2027 submission #217 (October 2026), p. 21, Theorem A.4 and its proof; p. 4, Section 2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/217.pdf

import Definitions.Def_MLAMaxDelay_RandomizedTimer_Timer

namespace MLAMaxDelay.RandomizedTimer.Supplement

open MeasureTheory

/-- Theorem A.4, p. 21: on every weighted rooted tree (one-leaf trees included), no randomized
online algorithm is γ-competitive against an oblivious adversary for any γ < e/(e−1). A
randomized algorithm is an arbitrary probability space of seeds and a causal algorithm for each
seed, with the cost measurable in the seed for each input (so that E[ALG(I)] is defined); the
input is chosen independently of the seed, outside the integral. -/
theorem randomized_lower_bound {V : Type} [Fintype V] [DecidableEq V]
    (T : WeightedTree V) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Input V → Schedule V) (hA : ∀ ω, Causal (A ω))
    (hmeas : ∀ I : Input V, Measurable (fun ω => cost T I (A ω I)))
    (γ : ℝ) (hγ : γ < Real.exp 1 / (Real.exp 1 - 1)) :
    ∃ I : Input V, ENNReal.ofReal γ * optimum T I < ∫⁻ ω, cost T I (A ω I) ∂μ := by sorry

end MLAMaxDelay.RandomizedTimer.Supplement
