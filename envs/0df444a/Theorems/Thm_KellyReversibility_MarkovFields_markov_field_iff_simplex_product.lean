-- Prove2me | Theorems.Thm_KellyReversibility_MarkovFields_markov_field_iff_simplex_product
-- name    : KellyReversibility.MarkovFields.markov_field_iff_simplex_product
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T03:29:36.656381+00:00
-- url     : https://prove2.me/theorems/44d9d0dc-6d17-480f-808e-7170d30f02be
-- title:
--   Theorem 9.2 — a random field is a Markov field iff $\pi(\mathbf n)=B\prod_{C\in\mathcal C}\phi_C(\mathbf n_C)$
-- statement:
--   Let $G$ be a graph on a finite set of sites, site $j$ carrying an attribute from a finite set $\mathcal N_j$, and let $\pi$ be a random field on $\mathcal S=\prod_j\mathcal N_j$ (strictly positive, summing to one). Let $\mathcal C$ be the set of simplices of $G$: the nonempty sets of sites any two distinct members of which are neighbours. Then $\pi$ is a Markov field, i.e.
--   $$P(n_j\mid\mathbf n_{G-j}) = P(n_j\mid\mathbf n_{\partial j})\qquad\text{for every site } j \text{ and state } \mathbf n, \qquad (9.2)$$
--   if and only if it can be written in the form
--   $$\pi(\mathbf n) = B\prod_{C\in\mathcal C}\phi_C(\mathbf n_C), \qquad \mathbf n\in\mathcal S, \qquad (9.5)$$
--   for some constant $B$ and some real functions $\phi_C$ of the attributes $\mathbf n_C$ of the sites in $C$.
--
--   This is the Hammersley–Clifford theorem for finite attribute sets: the conditional-independence structure of a positive random field given by its neighbourhood graph is the same as a factorization over the cliques of that graph. Kelly uses it to identify the equilibrium distributions of spatial processes.
--
--   **Formalization Note** $P(n_j\mid\mathbf n_{G-j})$ is the explicit ratio (9.1); $P(n_j\mid\mathbf n_{\partial j})$ is the conditional probability computed from $\pi$ by summing over the attributes of the non-neighbours. Simplices are nonempty cliques of the given graph $G$, not arbitrary sets of sites (with arbitrary sets every positive field factorizes trivially). Strict positivity of $\pi$ is a hypothesis; without it the "only if" direction fails (Kelly, Exercise 9.2.2).
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 186 (PDF 189), Theorem 9.2, Eq. (9.5); Markov field (9.2), p. 185

import Mathlib
import Definitions.Def_KellyReversibility_MarkovFields_RandomField

namespace KellyReversibility.MarkovFields

/-- **Theorem 9.2** (Kelly 1979, p. 186). Let `G` be a graph on the finite set of sites `V`,
let site `j` carry attributes from the finite set `N j`, and let `π` be a random field (strictly
positive, summing to one). Then `π` is a Markov field with respect to `G` (9.2) if and only if it
can be written in the form (9.5), `π(n) = B ∏_{C ∈ 𝒞} φ_C(n_C)`, where `𝒞` is the set of
simplices (nonempty cliques) of `G`. -/
theorem markov_field_iff_simplex_product {V : Type*} [Fintype V] [DecidableEq V]
    {N : V → Type*} [∀ j, Fintype (N j)] (G : SimpleGraph V)
    (π : ((j : V) → N j) → ℝ) (hπ : IsRandomField π) :
    IsMarkovField G π ↔ HasSimplexProductForm G π := by sorry

end KellyReversibility.MarkovFields
