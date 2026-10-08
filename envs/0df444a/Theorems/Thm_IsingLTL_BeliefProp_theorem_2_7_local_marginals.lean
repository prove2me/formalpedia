-- Prove2me | Theorems.Thm_IsingLTL_BeliefProp_theorem_2_7_local_marginals
-- name    : IsingLTL.BeliefProp.theorem_2_7_local_marginals
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:17:51.207961+00:00
-- url     : https://prove2.me/theorems/772e39db-c1d2-460b-822d-f985a6342968
-- title:
--   The BP fixed point approximates local marginals on tree-like neighbourhoods (Theorem 2.7)
-- statement:
--   Let $\beta\ge0$, $B>0$ and $\Delta\in\mathbb N$. There exist finite $c=c(\beta,B,\Delta)$ and $\lambda=\lambda(\beta,B,\Delta)>0$ such that the following holds. Let $G=(V,E)$ be a finite graph of maximal degree at most $\Delta$, $\nu^*$ a positive fixed point of the BP iteration (2.10), $i_*\in V$, $r,t\ge0$, $U=\mathsf B_{i_*}(r)$, and $j(i)$ a neighbour in $U$ of each $i\in\partial U$. If $\mathsf B_{i_*}(t)$ is a tree, then
--   $$\|\mu_U-\nu_U\|_{\mathrm{TV}}\le\exp\{c^{r+1}-\lambda(t-r)\},$$
--   where $\mu_U$ is the marginal on $U$ of the Ising model (1.1) and $\nu_U$ is the BP approximation (2.12).
--
--   Thus on locally tree-like graphs the BP fixed point computes local marginals with an error that decays exponentially in the radius $t$ of the tree-like neighbourhood.
--
--   **Formalization Note** The paper takes $\nu^*$ to be the fixed point of Theorem 2.6. The statement is made for every positive fixed point; by Theorem 2.6 started at such a fixed point, all positive fixed points coincide with that one, so this is the same statement without choosing a fixed point. $c^{r+1}$ is a power. For $r=0$ the border $\{i_*\}$ has no neighbour in $U$, so the statement is vacuous there, as is (2.12).
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 8, Theorem 2.7, eq. (2.13), with (2.12), p. 7

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_BPIteration
import Definitions.Def_IsingLTL_BeliefProp_BallApprox

namespace IsingLTL.BeliefProp

/-- **Theorem 2.7** (Dembo–Montanari, arXiv:0804.4726v3, p. 8, eq. (2.13), with (2.12) p. 7).
Assume `β ≥ 0`, `B > 0` and `G` is a graph of finite maximal degree `Δ`. Then there exist finite
`c = c(β, B, Δ)` and `λ = λ(β, B, Δ) > 0` such that for any `i* ∈ G` and `U = B_{i*}(r)`, if
`B_{i*}(t)` is a tree then `‖μ_U − ν_U‖_TV ≤ exp{c^{r+1} − λ(t − r)}`, where `μ_U` is the marginal
on `U` of the Ising model (1.1) and `ν_U` is the BP approximation (2.12) built from the fixed point
`ν*` of Theorem 2.6 and a choice `j(i)` of a neighbour in `U` of each border vertex `i ∈ ∂U`.

Formalization Note: `c, λ` are chosen before the graph. `G` is finite with degrees `≤ Δ`. The
statement is made for every **positive** BP fixed point `ν*` (a message family of distributions
with `bp ν* = ν*` and `ν*_{i→j}(+1) ≥ ν*_{i→j}(−1)`): by Theorem 2.6 started at such a `ν*`, every
positive fixed point is the fixed point of Theorem 2.6, so this is the paper's statement without
choosing that fixed point. `c^{r+1}` is a power. `t` and `r` are arbitrary naturals (`t ≤ r` is
allowed; `t − r` is computed in `ℝ`). For `r = 0` the border `{i*}` has no neighbour in `U`, so
the hypothesis on `j` cannot hold and the statement is vacuous, as `(2.12)` is undefined there. -/
theorem theorem_2_7_local_marginals (β B : ℝ) (Δ : ℕ) (hβ : 0 ≤ β) (hB : 0 < B) :
    ∃ c lam : ℝ, 0 < lam ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        (∀ v, G.degree v ≤ Δ) →
        ∀ νstar : V → V → Bool → ℝ, IsMsgFamily G νstar → IsPositiveMsg G νstar →
          bp G β B νstar = νstar →
          ∀ (istar : V) (r t : ℕ) (jsel : V → V),
            (∀ i ∈ border G istar r, G.Adj i (jsel i) ∧ jsel i ∈ ball G istar r) →
            IsTreeBall G istar t →
            tvDist (muU G β B istar r) (nuU G β B νstar istar r jsel) ≤
              Real.exp (c ^ (r + 1) - lam * ((t : ℝ) - r)) := by sorry

end IsingLTL.BeliefProp
