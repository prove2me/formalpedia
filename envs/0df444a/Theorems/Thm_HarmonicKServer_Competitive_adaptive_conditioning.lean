-- Prove2me | Theorems.Thm_HarmonicKServer_Competitive_adaptive_conditioning
-- name    : HarmonicKServer.Competitive.adaptive_conditioning
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:01:01.221186+00:00
-- url     : https://prove2.me/theorems/3412d77a-3646-4b41-9efc-28a64cce4a7b
-- title:
--   §2 — Random-tape interaction and expectation bridge
-- statement:
--   Fix $k\ge1$, initial configurations, and any probability space of private adversary seeds. Each seed selects a valid causal service policy, with measurable scalar history weights and costs. For every $N$, the concrete joint seed-and-label-history law is a probability measure, and its online and adversary cost integrals equal their mixed tree expectations:
--   $$\mathbb E_{\rm joint}C_{\rm H}=\int_\Omega\mathbb E[C_{\rm H}\mid\omega],d\mu(\omega),\qquad
--   \mathbb E_{\rm joint}C_{\rm ADV}=\int_\Omega\mathbb E[C_{\rm ADV}\mid\omega],d\mu(\omega).$$
--   If the same nonnegative constants $\rho,B$ bound every seeded policy's expected online cost by $\rho$ times its expected adversary cost plus $B$, then they bound the full randomized adaptive interaction for all finite horizons. The seed is arbitrary and the policies can react to every completed online label; neither policy support nor metric space is finite. This makes the source's conditioning on completed service and the extension to randomized adaptive adversaries explicit.
--
--   Differences from the source:
--   - encoding: an arbitrary randomized causal adversary → an arbitrary probability-space random tape selecting full label-history policies, with a concrete joint law; reason: private randomness can be fixed before play while requests and service remain functions of all completed online choices; integrating the tree laws gives the same randomized interaction
--   - encoding: expectations → nonnegative extended integrals of measurable scalar costs; reason: these are genuine expectations, including infinite expected adversary costs; no real-integral default is used
-- source:
--   Yichen Huang, STOC 2027 submission #95 (October 2026), p. 3, §2 adaptive interaction and conditioning; Lemma 2.3 expectation formulation, p. 4 (unnumbered bridge) (PDF p. 4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/95.pdf; pinned PDF SHA256 20635ef9c29593d01fa406f1a63fdc6b98250e5fc1b1b5c4ed088b407a4e8fd6. Title-page date: November 3, 2026; canonical metadata citation: October 2026.

import Definitions.Def_HarmonicKServer_Competitive_Interaction

namespace HarmonicKServer.Competitive
open scoped BigOperators ENNReal
open MeasureTheory

/-- Section 2's conditioning on completed service, made explicit for arbitrary random tapes. -/
theorem adaptive_conditioning {k : ℕ} (hk : 1 ≤ k) {V Ω : Type*}
    [MetricSpace V] [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Adversary k V) (X Y : KServer.Config k V) (hA : MeasurableMixture μ A X Y) :
    (∀ N, IsProbabilityMeasure (interactionLaw μ A X Y N)) ∧
    (∀ N,
      (∫⁻ z, ENNReal.ofReal (stateAt (A z.1) X Y (List.ofFn z.2)).onlineCost
        ∂interactionLaw μ A X Y N) = mixedOnline μ A X Y N) ∧
    (∀ N,
      (∫⁻ z, ENNReal.ofReal (stateAt (A z.1) X Y (List.ofFn z.2)).adversaryCost
        ∂interactionLaw μ A X Y N) = mixedAdversary μ A X Y N) ∧
    (∀ (ρ B : ℝ), 0 ≤ ρ → 0 ≤ B →
      (∀ (ω : Ω) (N : ℕ), onlineExpectation (A ω) X Y N ≤
        ENNReal.ofReal ρ * adversaryExpectation (A ω) X Y N + ENNReal.ofReal B) →
      ∀ N, mixedOnline μ A X Y N ≤
        ENNReal.ofReal ρ * mixedAdversary μ A X Y N + ENNReal.ofReal B) := by sorry

end HarmonicKServer.Competitive
