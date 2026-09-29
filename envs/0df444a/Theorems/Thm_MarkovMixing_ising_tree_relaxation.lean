-- Prove2me | Theorems.Thm_MarkovMixing_ising_tree_relaxation
-- name    : MarkovMixing.ising_tree_relaxation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:27:23.240727+00:00
-- url     : https://prove2.me/theorems/fd2006c5-92cc-4361-bcb5-74adbfaba1e0
-- title:
--   Polynomial relaxation time on trees (Kenyon--Mossel--Peres)
-- statement:
--   Let $T_{b,k}$ be the rooted $b$-ary tree of depth $k$ ($b\ge2$, $k\ge1$): vertices are the words of length at most $k$ over a $b$-letter alphabet, each word joined to its $b$ one-letter extensions; write $n_k$ for its number of vertices. The **Ising model** on $T_{b,k}$ at inverse temperature $\beta>0$ is the distribution $\pi(\sigma)\propto\exp\bigl(\beta\sum_{\{v,w\}\in E}\sigma(v)\sigma(w)\bigr)$ on spin configurations, with **Glauber dynamics** re-sampling a uniformly chosen site from the conditional distribution. Among the eigenvalues of the dynamics (real $\lambda$ with $Pf=\lambda f$, $f\ne0$), let $\lambda_\star$ be the largest absolute value of an eigenvalue different from $1$; the **relaxation time** is $t_{\mathrm{rel}}=(1-\lambda_\star)^{-1}$, as in Mission VII.
--
--   The theorem (Theorem 15.6, Kenyon–Mossel–Peres; Levin–Peres–Wilmer) asserts the polynomial bound
--   $$t_{\mathrm{rel}}\;\le\;n_k^{\;c_T(\beta,b)},\qquad c_T(\beta,b)=\frac{2\beta(3b+1)}{\log b}+1.$$
--
--   On trees the relaxation time stays polynomial in the volume at **every** temperature — unlike the complete graph, where it becomes exponential below the critical temperature. The book's proof is an induction on depth powered by this mission's other tools: cutting the root's edges (the edge-removal proposition) splits the tree into independent subtrees whose product structure is handled by a block-dynamics comparison, at a per-level cost of $e^{2\beta(3b+1)}$ — which telescopes to the stated exponent.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 15.4, Theorem 15.6, p. 207

import Definitions.Def_mm_ising
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace MarkovMixing

/-- **Theorem 15.6** (Kenyon–Mossel–Peres; LPW): for the Glauber dynamics of
the Ising model on the rooted `b`-ary tree of depth `k`, with
`c_T(β,b) = 2β(3b+1)/log b + 1` and `n_k` the number of vertices,
`t_rel ≤ n_k^{c_T(β,b)}`. -/
theorem ising_tree_relaxation (b k : ℕ) (hb : 2 ≤ b) (hk : 1 ≤ k)
    (β : ℝ) (hβ : 0 < β) [inst : DecidableRel (aryTree b k).Adj] :
    relaxationTime (glauber (isingDist (aryTree b k) β)) ≤
      (Fintype.card (TreeVertex b k) : ℝ) ^
        (2 * β * (3 * (b : ℝ) + 1) / Real.log b + 1) := by
  sorry

end MarkovMixing
