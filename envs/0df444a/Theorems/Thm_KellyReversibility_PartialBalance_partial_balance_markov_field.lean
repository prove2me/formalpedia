-- Prove2me | Theorems.Thm_KellyReversibility_PartialBalance_partial_balance_markov_field
-- name    : KellyReversibility.PartialBalance.partial_balance_markov_field
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:01:09.399579+00:00
-- url     : https://prove2.me/theorems/cd0caffd-470d-4ae4-8652-81f7c41dae91
-- title:
--   Corollary 9.7 — partial balance at every site makes the equilibrium distribution a Markov field
-- statement:
--   Let $\mathbf n(t)$ be a spatial process over a finite graph $G$ with finite attribute sets, a state space with at least two states, rates $q$ and equilibrium distribution $\pi$. If $\pi$ satisfies the partial balance equations
--   $$\pi(\mathbf n)\sum_m q(\mathbf n,T_j^m\mathbf n)=\sum_m\pi(T_j^m\mathbf n)q(T_j^m\mathbf n,\mathbf n),\qquad\mathbf n\in\mathcal S\tag{9.26}$$
--   for each site $j\in G$, then $\pi$ is a Markov field over $G$: the conditional probability
--   $$P(n_j\mid\mathbf n_{G-j})=\frac{\pi(\mathbf n)}{\sum_{m\in\mathcal N_j}\pi(T_j^m\mathbf n)}$$
--   depends on $\mathbf n_{G-j}$ only through the attributes $\mathbf n_{\partial j}$ of the neighbours of $j$. The probabilities obey $0<\pi(\mathbf n)<1$, as in the book's random-field definition.
--
--   This strengthens Theorem 9.3 (the equilibrium distribution of a reversible spatial process is a Markov field): detailed balance is replaced by the weaker partial balance at each site.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 202, Corollary 9.7

import Mathlib
import Definitions.Def_KellyReversibility_PartialBalance_Core
import Definitions.Def_KellyReversibility_PartialBalance_Spatial

namespace KellyReversibility.PartialBalance

/-- **Corollary 9.7** (Kelly 1979, p. 202). If the equilibrium distribution `π` of a spatial
process over the graph `G` satisfies the partial balance equations (9.26) for each site `j`,
then `π` is a Markov field over `G`. The state space has at least two states, as required by
the book's random-field codomain `(0,1)` on p. 184. -/
theorem partial_balance_markov_field {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → Type*} [∀ i, Fintype (N i)] [∀ i, DecidableEq (N i)]
    (G : SimpleGraph ι) (q : (∀ i, N i) → (∀ i, N i) → ℝ) (hsp : IsSpatialProcess G q)
    (π : (∀ i, N i) → ℝ) (hπ : IsEquilibriumDist q π)
    (hstates : ∃ n n' : (∀ i, N i), n ≠ n')
    (hpb : ∀ j : ι, SitePartialBalance π q j) :
    IsMarkovField G π := by sorry

end KellyReversibility.PartialBalance
