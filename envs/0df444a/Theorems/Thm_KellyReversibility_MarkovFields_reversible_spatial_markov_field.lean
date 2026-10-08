-- Prove2me | Theorems.Thm_KellyReversibility_MarkovFields_reversible_spatial_markov_field
-- name    : KellyReversibility.MarkovFields.reversible_spatial_markov_field
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T03:29:23.783279+00:00
-- url     : https://prove2.me/theorems/09f158f2-e8d6-4592-b044-1aaa9edf11f1
-- title:
--   Theorem 9.3 — the equilibrium distribution of a reversible spatial process is a Markov field
-- statement:
--   Let $G$ be a graph on a finite set of sites, site $j$ carrying attributes from a finite set $\mathcal N_j$. Let $q$ be the transition rates of a **spatial process** with respect to $G$: nonnegative, with $q(\mathbf n,\mathbf n)=0$, and satisfying conditions (i)–(iii) of §9.2 (one site changes at a time; $q(\mathbf n,T_j^m\mathbf n)$ depends on $\mathbf n$ only through $n_j$ and $\mathbf n_{\partial j}$; $T_j^m\mathbf n$ is reachable from $\mathbf n$ by positive-rate jumps that change only site $j$). Let $\pi$ be a random field (positive, summing to one) in detailed balance with $q$:
--   $$\pi(\mathbf n)\,q(\mathbf n,\mathbf n') = \pi(\mathbf n')\,q(\mathbf n',\mathbf n)\qquad\text{for all }\mathbf n,\mathbf n'\in\mathcal S.$$
--   Then $\pi$ is a **Markov field** with respect to $G$: $P(n_j\mid\mathbf n_{G-j}) = P(n_j\mid\mathbf n_{\partial j})$ for every site $j$ and state $\mathbf n$.
--
--   The theorem explains when a locally interacting stochastic process has a Markov field as its equilibrium distribution; condition (iii) cannot be dropped (Kelly, Exercise 9.2.2).
--
--   **Formalization Note** This is the rate-level reading of the book's statement. A positive distribution summing to one is the equilibrium distribution of a process and the process is reversible exactly when the detailed balance equations hold (Kelly, Theorem 1.3); the statement assumes detailed balance and does not formalize the process itself. Irreducibility of the process follows from condition (iii) on a finite state space. Detailed balance is the published `KellyStochasticNetworks.DetailedBalance π q` (π first).
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 189 (PDF 192), Theorem 9.3; definition of spatial process, p. 189

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_MarkovFields_RandomField
import Definitions.Def_KellyReversibility_MarkovFields_SpatialProcess

namespace KellyReversibility.MarkovFields

/-- **Theorem 9.3** (Kelly 1979, p. 189). The equilibrium distribution of a reversible spatial
process is a Markov field. Rate-level reading: `q` are the transition rates of a spatial process
with respect to `G` (conditions (i)–(iii) of p. 189; nonnegative, with `q(n, n) = 0`), and `π`
is a random field (positive, summing to one) in detailed balance with `q`, which is what it means
for `π` to be the equilibrium distribution of the process and for the process to be
reversible (Kelly, Theorem 1.3). Then `π` is a Markov field with respect to `G`. -/
theorem reversible_spatial_markov_field {V : Type*} [Fintype V] [DecidableEq V]
    {N : V → Type*} [∀ j, Fintype (N j)] (G : SimpleGraph V)
    (q : ((j : V) → N j) → ((j : V) → N j) → ℝ)
    (hq_nonneg : ∀ n n', 0 ≤ q n n') (hq_diag : ∀ n, q n n = 0)
    (hspatial : IsSpatialProcess G q)
    (π : ((j : V) → N j) → ℝ) (hπ : IsRandomField π)
    (hdb : KellyStochasticNetworks.DetailedBalance π q) :
    IsMarkovField G π := by sorry

end KellyReversibility.MarkovFields
