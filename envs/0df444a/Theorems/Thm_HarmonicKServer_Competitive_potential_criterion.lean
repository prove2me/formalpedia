-- Prove2me | Theorems.Thm_HarmonicKServer_Competitive_potential_criterion
-- name    : HarmonicKServer.Competitive.potential_criterion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:01:17.616471+00:00
-- url     : https://prove2.me/theorems/d022384c-2589-43c3-b947-e776cc127bf3
-- title:
--   Lemma 2.3 — Potential criterion
-- statement:
--   Let $k\ge2$ and consider any randomized server algorithm's execution against a lazy adaptive online adversary whose configurations have distinct locations. Let $\phi$ be a finite nonnegative potential invariant under relabelling either tuple. Suppose $\rho\ge1$, the one-label adversary movement bound holds at factor $\rho$, and the conditional online potential decrease pays for the online cost after the adversary has served. For all finite horizons $N$,
--   $$\mathbb E[C_{\rm ALG}(N)]\le\rho\mathbb E[C_{\rm ADV}(N)]+\phi(X_0,Y_0).$$
--   The initial potential is the particular additive constant, fixed before all rounds. The execution and its online service schedules are arbitrary; this criterion does not replace the actual algorithm in Theorem 1.1.
--
--   **Formalization Note** Conditional drift is tested against every event known before the fresh online action, using the equivalent nonnegative inequality $\mathbb E[\mathbf1_D(c+\phi_{\rm after})]\le\mathbb E[\mathbf1_D\phi_{\rm before}]$. This avoids undefined differences of infinite expectations. Scalar observables carry the standard measurability convention required by the source's expectations; neither integrability nor bounded costs are assumed.
--
--   Differences from the source:
--   - encoding: labels [k] with k at least two in Sections 2–5 → Fin k and an explicit 2 ≤ k hypothesis; reason: the finite label change is a bijection; this is the source analysis regime, not a restriction on the headline goal
--   - encoding: an arbitrary randomized algorithm admitting the two potential properties → an arbitrary probability-space execution with charged moves and conditional drift on its pre-online sigma algebras; reason: applying the universally quantified execution result to every run gives exactly the algorithm criterion, with no finite-action restriction
--   - encoding: expected costs and conditional potential decrease → nonnegative extended integrals and conditional cost-plus-potential inequalities; reason: these preserve finite expectations and also cover infinite expected costs without subtracting infinities
-- source:
--   Yichen Huang, STOC 2027 submission #95 (October 2026), p. 4, Lemma 2.3 (PDF p. 5); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/95.pdf; pinned PDF SHA256 20635ef9c29593d01fa406f1a63fdc6b98250e5fc1b1b5c4ed088b407a4e8fd6. Title-page date: November 3, 2026; canonical metadata citation: October 2026.

import Definitions.Def_HarmonicKServer_Competitive_Framework

namespace HarmonicKServer.Competitive
open scoped BigOperators ENNReal
open MeasureTheory

/-- Lemma 2.3 on an arbitrary randomized execution, not restricted to Harmonic. -/
theorem potential_criterion {k : ℕ} (hk : 2 ≤ k) {V Ω : Type*}
    [MetricSpace V] [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X₀ Y₀ : KServer.Config k V) (P : ServerExecution k V Ω μ X₀ Y₀)
    (φ : KServer.Config k V → KServer.Config k V → ℝ)
    (hφ : ∀ X Y, 0 ≤ φ X Y) (hperm : PermutationInvariant φ)
    (ρ : ℝ) (hρ : 1 ≤ ρ) (hadv : AdversaryMovement φ ρ)
    (hlazy : ExecutionLazy P) (hdistinct : ∀ t ω, Function.Injective (P.Y t ω))
    (honline : ConditionalOnlineMovement P φ) :
    ∀ N, executionOnlineCost P N ≤
      ENNReal.ofReal ρ * executionAdversaryCost P N + ENNReal.ofReal (φ X₀ Y₀) := by sorry

end HarmonicKServer.Competitive
