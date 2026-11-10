-- Prove2me | Theorems.Thm_LocalOccupancyIS_Glauber_lemma_7
-- name    : LocalOccupancyIS.Glauber.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:58:12.677902+00:00
-- url     : https://prove2.me/theorems/92c46539-6cce-4a2d-afe0-e55c4e966829
-- title:
--   Lemma 7 — heat-bath entropy identity and total variation
-- statement:
--   Let $G$ be a finite simple graph, $\lambda>0$, $\pi$ its hard-core law, $u$ a vertex, and $\nu$ any normalized probability law on independent sets. For the single-site heat-bath kernel $P_u$ and the open-neighborhood conditional kernel $Q_u$, each choice $A\in\{P_u,Q_u\}$ satisfies
--
--   $$D_{KL}(\nu\|\pi)-D_{KL}(\nu A\|\pi)=D_{KL}(\nu\|\nu A)\ge2d_{TV}(\nu,\nu A)^2.$$
--
--   The hard-core law is normalized, both kernels are stochastic, and the required domination of $\nu$ by $\pi$ and by $\nu A$ is asserted as a conclusion. Thus no full-support assumption on $\nu$ is used. Entropy is measured in nats and total variation is half the L¹ distance. The identity and Pinsker bound supply the entropy accounting in the transfer theorem.
--
--   Differences from the source:
--   - encoding: finite independent sets and induced subgraphs → Boolean configurations on finite types and induced subtypes; reason: these presentations preserve all feasible configurations, including the empty one
--   - encoding: relative entropy of the finite heat-bath probability laws → real finite entropy sums together with explicit normalization, stochasticity and domination conclusions; reason: positive fugacity makes these entropies finite even for point-mass input laws; singular-law junk values are not used
-- source:
--   Ewan Davies, Brian Tan, STOC 2027 submission #982 (October 2026), Lemma 7, p. 12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/982.pdf#page=12

import Definitions.Def_LocalOccupancyIS_Glauber_Dynamics

namespace LocalOccupancyIS.Glauber
/-- Lemma 7, p.12; domination and normalization are conclusions, never input restrictions. -/
theorem lemma_7 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) (hlam : 0 < lam)
    (u : V) (ν : State G → ℝ) (hν : MarkovMixing.IsDist ν) :
    MarkovMixing.IsDist (HardCoreBochner.hcLaw G lam) ∧
    Dominated ν (HardCoreBochner.hcLaw G lam) ∧
    ∀ A ∈ [P G lam u, Q G lam u],
      MarkovMixing.IsStochastic A ∧ Dominated ν (push ν A) ∧
      kl ν (HardCoreBochner.hcLaw G lam) - kl (push ν A) (HardCoreBochner.hcLaw G lam) =
        kl ν (push ν A) ∧ kl ν (push ν A) ≥ 2 * tv ν (push ν A) ^ 2 := by sorry
end LocalOccupancyIS.Glauber
