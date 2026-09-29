-- Prove2me | Theorems.Thm_MarkovEntanglement_rmab_index_policy_entanglement_le_sqrt
-- name    : MarkovEntanglement.rmab_index_policy_entanglement_le_sqrt
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-28T02:24:13.55194+00:00
-- url     : https://prove2.me/theorems/584c9896-1117-4973-8141-83f152d65cf8
-- title:
--   Index policies are asymptotically separable (Thm. 7)
-- statement:
--   Consider an $N$-agent restless multi-armed bandit: homogeneous agents sharing a local state space $S$ and a pair of local kernels $P_0, P_1$, each agent choosing between idle and activate, and a budget that activates the fraction $\alpha$ of the agents at every step. Fix an injective priority index $\nu$ and let $\pi$ be the index policy it induces for the budget $\lfloor \alpha N \rfloor$. Assume the two standard technical conditions, both stated for the explicit mean-field map of the configuration process at activation fraction $\alpha$ — properties of the limit model, quantified before the constant and before $N$:
--
--   1. **Uniform global attractor property (UGAP):** the map admits a fixed point $m^\ast$ that attracts every initial configuration, uniformly in the initial point.
--   2. **Mean-field non-degeneracy:** at $m^\ast$ the budget runs out strictly inside some state, $0 < \alpha - \sum_{\nu_y > \nu_x} m^\ast_y < m^\ast_x$, so the limiting policy genuinely randomises there.
--
--   Then there is a constant $C$, **independent of $N$**, such that for every stationary occupancy distribution $\mu^\pi_{1:N}$ of the induced chain and every agent $i$, the measure of Markov entanglement of the joint chain, with respect to the occupancy-weighted agent-wise total variation distance, satisfies
--
--   $$\mathcal{E}_i(P^\pi_{1:N}) \;\le\; \frac{C}{\sqrt{N}}.$$
--
--   Index policies are therefore *asymptotically separable*: their joint transition matrix approaches the separable ones as the system grows, at rate $1/\sqrt{N}$.
--
--   The proof assembles the preceding milestones. Lemma 8 reduces the entanglement to the expected deviation $\mathbb{E}[\|m - m^\ast\|_\infty]$ of the configuration from the mean-field fixed point under the stationary distribution. Lemma 9 gives the per-step fluctuation of the configuration, of order $1/\sqrt{N}$. Lemma 10 propagates it over a horizon, and Lemma 11 supplies both a uniform horizon at which every trajectory has entered a neighbourhood of $m^\ast$ and the contraction that stops the propagated error from compounding. What comes out is a stationary deviation of order $1/\sqrt{N}$ with a constant built from the local kernels, the priority index, the activation fraction and the contraction rate — none of which involve $N$.
--
--   Combined with the general decomposition bound of the companion mission, this yields Corollary 1: the value decomposition error of an index policy is sublinear in $N$.
--
--   The stationary distribution is assumed **exchangeable** — invariant under permuting the agents. The source's proof exchanges agent indices and asserts the stationary distribution is unchanged, which is exactly exchangeability; it holds automatically for the unique stationary distribution of an ergodic symmetric chain, but a reducible chain also has non-exchangeable stationary distributions concentrated on asymmetric closed classes, for which the agent-averaging step (and with it the stated bound) is not available. The hypothesis records precisely the consequence of ergodicity the argument uses.
-- source:
--   Shuze Chen and Tianyi Peng, 'Multi-agent Markov Entanglement', arXiv:2506.02385v3, Section 7.1, p. 24, Theorem 7

import Mathlib
import Definitions.Def_markov_entanglement_meanfield

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglement

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Theorem 7 (Chen and Peng, Section 7.1, p. 24).  For an index policy satisfying the uniform
global attractor property and non-degeneracy there is a constant `C`, independent of `N`, with

`Eᵢ(P^π_{1:N}) ≤ C / √N`

for every agent `i`: the measure of Markov entanglement of the `N`-agent chain vanishes as the
system grows, so index policies are asymptotically separable.  The two technical conditions
are stated for the explicit mean-field map at the activation fraction `α` — properties of the
limit model, quantified before `C` and before `N`.  This is Lemma 8 combined with the `1/√N`
concentration of the configuration around the mean-field fixed point. -/
theorem rmab_index_policy_entanglement_le_sqrt
    (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0) (hP1 : IsTransitionMatrix P1)
    (ν : S → ℝ) (hν : Function.Injective ν) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (mstar : S → ℝ) (hmstar : IsConfiguration mstar)
    (hUGAP : IsUniformGlobalAttractor (meanFieldMap P0 P1 ν α) mstar)
    (hnd : IsNonDegenerateMeanField ν α mstar) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ), 0 < N →
        ∀ (π : (Fin N → S) → (Fin N → Bool) → ℝ),
          IsIndexPolicy ν ⌊α * (N : ℝ)⌋₊ π →
          ∀ (μ : Joint (StateAction (fun _ : Fin N => S) (fun _ : Fin N => Bool)) → ℝ),
            IsDist μ →
            IsExchangeableDist μ →
            IsStationary (inducedTransition
              (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π) μ →
            ∀ i : Fin N,
              entanglementN i μ (inducedTransition
                  (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π)
                ≤ C / Real.sqrt (N : ℝ) := by
  sorry

end MarkovEntanglement
