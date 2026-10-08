-- Prove2me | Theorems.Thm_KellyReversibility_MarkovFields_conditionals_determine_field
-- name    : KellyReversibility.MarkovFields.conditionals_determine_field
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T03:29:22.288002+00:00
-- url     : https://prove2.me/theorems/0ed670ca-c3cb-4800-bb06-790aa7baeb99
-- title:
--   Lemma 9.1 — the conditional probabilities $P(n_j\mid\mathbf n_{G-j})$ determine the random field
-- statement:
--   Let sites $j$ in a finite set carry attributes from finite sets $\mathcal N_j$, with state space $\mathcal S=\prod_j\mathcal N_j$, and let $\pi$ and $\pi'$ be random fields on $\mathcal S$ (strictly positive, summing to one). Write $P_\pi(n_j\mid\mathbf n_{G-j}) = \pi(\mathbf n)/\sum_{m\in\mathcal N_j}\pi(T_j^m\mathbf n)$ for the conditional probabilities (9.1). If
--   $$P_\pi(n_j\mid\mathbf n_{G-j}) = P_{\pi'}(n_j\mid\mathbf n_{G-j}) \qquad\text{for every site } j \text{ and every } \mathbf n\in\mathcal S,$$
--   then $\pi = \pi'$.
--
--   In words: the conditional probabilities of each site given all the others determine a positive random field uniquely. This is the reason the local conditional laws are a legitimate way to specify a random field, and it is the starting point of the factorization in Theorem 9.2.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 185 (PDF 188), Lemma 9.1

import Mathlib
import Definitions.Def_KellyReversibility_MarkovFields_RandomField

namespace KellyReversibility.MarkovFields

/-- **Lemma 9.1** (Kelly 1979, p. 185). The conditional probabilities `P(n_j | n_{G-j})` of
(9.1), `j ∈ G`, `n ∈ 𝒮`, determine the random field `π` uniquely: two random fields on the same
finite state space with the same conditional probabilities are equal. -/
theorem conditionals_determine_field {V : Type*} [Fintype V] [DecidableEq V] {N : V → Type*}
    [∀ j, Fintype (N j)] (π π' : ((j : V) → N j) → ℝ)
    (hπ : IsRandomField π) (hπ' : IsRandomField π')
    (hcond : ∀ (j : V) (n : (k : V) → N k), condProb π j n = condProb π' j n) :
    π = π' := by sorry

end KellyReversibility.MarkovFields
