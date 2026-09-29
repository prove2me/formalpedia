-- Prove2me | Theorems.Thm_MarkovMixing_ising_edge_removal
-- name    : MarkovMixing.ising_edge_removal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:26:11.990582+00:00
-- url     : https://prove2.me/theorems/4e77ca24-a0c3-4989-bfb6-90400071f3ff
-- title:
--   Edge removal perturbs the spectral gap by at most $e^{2\beta(\Delta+2r)}$
-- statement:
--   Let $G$ be a graph with maximum degree $\Delta$ on a finite vertex set, and let $G'\subseteq G$ be a subgraph obtained by deleting $r$ edges (all vertices kept). For a graph $H$, the **Ising model** at inverse temperature $\beta>0$ is the distribution $\pi_H(\sigma)\propto\exp\bigl(\beta\sum_{\{v,w\}\in E(H)}\sigma(v)\sigma(w)\bigr)$ on spin configurations $\sigma:V\to\{\pm1\}$, and its **Glauber dynamics** re-samples a uniformly chosen site from the conditional distribution. The **spectral gap** of a chain is $\gamma=1-\lambda_2$, where $\lambda_2$ is the largest eigenvalue different from $1$ (an eigenvalue being a real $\lambda$ with $Pf=\lambda f$ for some nonzero $f$, as in Mission VII).
--
--   The theorem (Proposition 15.7 of Levin–Peres–Wilmer) asserts that deleting the $r$ edges changes the spectral gap by at most an explicit exponential factor:
--   $$\gamma_{G'}\;\le\;e^{\,2\beta(\Delta+2r)}\;\gamma_{G},$$
--   where $\gamma_H$ denotes the gap of the Glauber dynamics for the Ising model on $H$.
--
--   The proof is a direct comparison of Dirichlet forms (Mission VII): removing $r$ edges changes every Gibbs weight by at most $e^{2\beta r}$ and every transition probability by at most $e^{2\beta\Delta}$. In the book this is the key surgery step for the tree bound: cutting the root's edges splits the tree into independent subtrees, at a bounded cost in the gap.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 15.4, Proposition 15.7, p. 207

import Definitions.Def_mm_ising

namespace MarkovMixing

/-- **Proposition 15.7** (LPW): removing `r` edges from a graph of maximal
degree `Δ` changes the spectral gap of the Ising Glauber dynamics by at most
a factor `e^{2β(Δ + 2r)}`:  `γ̃ ≤ e^{2β(Δ+2r)} γ` is equivalent to the
stated `1/γ ≤ e^{2β(Δ+2r)}/γ̃`. -/
theorem ising_edge_removal {Vv : Type*} [Fintype Vv] [DecidableEq Vv]
    [Nonempty Vv] (G G' : SimpleGraph Vv) [DecidableRel G.Adj]
    [DecidableRel G'.Adj] (hsub : G' ≤ G) (β : ℝ) (hβ : 0 < β) :
    spectralGap (glauber (isingDist G' β)) ≤
      Real.exp (2 * β * ((G.maxDegree : ℝ) +
        2 * ((G.edgeFinset \ G'.edgeFinset).card : ℝ))) *
      spectralGap (glauber (isingDist G β)) := by
  sorry

end MarkovMixing
