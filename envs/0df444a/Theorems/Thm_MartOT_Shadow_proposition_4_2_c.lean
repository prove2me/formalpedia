-- Prove2me | Theorems.Thm_MartOT_Shadow_proposition_4_2_c
-- name    : MartOT.Shadow.proposition_4_2_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:36.708574+00:00
-- url     : https://prove2.me/theorems/11c98c76-16d5-4cbb-8bd3-81ef08649f46
-- title:
--   Proposition 4.2, third bullet, p. 21 — with fixed mass and mean, convergence in 𝓜 is pointwise convergence of potentials
-- statement:
--   Let $\mathcal M$ be the finite Borel measures on $\mathbb R$ with finite first moment, with the topology of weak convergence in $\mathcal M$ (weak convergence together with convergence of $\int|x|$), and for $\mu\in\mathcal M$ let the **potential function** $u_\mu(x)=\int|y-x|\,d\mu(y)$.
--
--   Let $(\mu_n)_{n\in\mathbb N}$ be a sequence in $\mathcal M$ such that every $\mu_n$ has mass $k$ and mean $m$, i.e. $\mu_n(\mathbb R)=k$ and $\int x\,d\mu_n=km$. Then:
--
--   1. for every $\mu\in\mathcal M$, $(\mu_n)_n$ converges weakly in $\mathcal M$ to $\mu$ if and only if
--   $$u_{\mu_n}(x)\longrightarrow u_\mu(x)\quad\text{for every }x\in\mathbb R;$$
--   2. if $(\mu_n)_n$ converges weakly in $\mathcal M$ to $\mu$ and $(u_{\mu_n})_n$ converges pointwise to $u_{\mu'}$ for some $\mu'\in\mathcal M$, then $\mu=\mu'$.
--
--   Together, these say that $(\mu_n)_n$ converges in $\mathcal M$ to some $\mu$ exactly when its potential functions converge pointwise to the potential function of some $\mu'\in\mathcal M$, and that then $\mu=\mu'$. It is the compactness tool behind the limit arguments of Section 4.
--
--   **Formalization Note** The page's "converges to some $\mu$ iff the potentials converge pointwise to the potential of some $\mu'$; in that case $\mu=\mu'$" is stated as the two clauses above, which together are equivalent to it. "Mean $m$" is written $\int x\,d\mu_n=km$, which is the mean condition when $k>0$ and is vacuous when $k=0$ (all $\mu_n$ are then zero).
-- source:
--   arXiv:1208.1509v2, Proposition 4.2 (third bullet), p. 21

import Mathlib
import Definitions.Def_MartOT_Var_Setting
import Definitions.Def_MartOT_Shadow_ConvergesInM

namespace MartOT.Shadow

open MeasureTheory Filter Topology

theorem proposition_4_2_c (μs : ℕ → Measure ℝ) (k m : ℝ) (hμs : ∀ n, MartOT.Var.InM (μs n))
    (hk : ∀ n, (μs n Set.univ).toReal = k) (hm : ∀ n, ∫ x, x ∂(μs n) = k * m) :
    (∀ μ : Measure ℝ, MartOT.Var.InM μ →
      (ConvergesInM μs μ ↔
        ∀ x : ℝ, Tendsto (fun n => MartOT.Var.potential (μs n) x) atTop (𝓝 (MartOT.Var.potential μ x)))) ∧
    (∀ μ μ' : Measure ℝ, MartOT.Var.InM μ → MartOT.Var.InM μ' → ConvergesInM μs μ →
      (∀ x : ℝ, Tendsto (fun n => MartOT.Var.potential (μs n) x) atTop (𝓝 (MartOT.Var.potential μ' x))) →
      μ = μ') := by sorry

end MartOT.Shadow
