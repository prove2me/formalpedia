-- Prove2me | Theorems.Thm_MLRPCake_EnvyFree_lemma_2
-- name    : MLRPCake.EnvyFree.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:14.476598+00:00
-- url     : https://prove2.me/theorems/5bb7e8c0-e297-4f36-8b4b-d3e512f78abb
-- title:
--   Lemma 2, p. 11 — some x̂ ∈ (0,1) has RD_n(x̂) = 1 − δ, and every such x̂ initializes a δ-ripple division
-- statement:
--   Let $\mathcal C=\langle[n],\{f_i\}_i\rangle$ be a cake-division instance with $n\ge2$ agents whose cut and eval queries are $\lambda$-Lipschitz for some $\lambda\ge1$, and let $\delta\in(0,1)$. Then:
--
--   1. there is a point $\hat x\in(0,1)$ with
--   $$\mathrm{RD}_n(\hat x)=1-\delta;$$
--   2. every point $\hat x\in(0,1)$ with $\mathrm{RD}_n(\hat x)=1-\delta$ initializes a $\delta$-ripple division: the points $x_0=0$, $x_1=\hat x$ and $x_i=\mathrm{RD}_i(\hat x)$ for $2\le i\le n$ form a $\delta$-ripple division of $\mathcal C$.
--
--   This gives the universal existence of $\delta$-ripple divisions for every $\delta>0$, independently of MLRP.
--
--   **Formalization Note** No MLRP hypothesis, as on the page. The positivity $v_i(x_{i-1},x_i)>0$ required by Definition 2 has to come from the Lipschitz continuity of the cut queries. $\lambda\ge1$ is the paper's standing assumption.
-- source:
--   Barman & Rathi, Fair Cake Division Under Monotone Likelihood Ratios, arXiv:2006.00481v3, p. 11, Lemma 2 (proof pp. 11–12)

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model

namespace MLRPCake.EnvyFree

/-- Lemma 2, p. 11: with `λ`-Lipschitz queries and `δ ∈ (0,1)`, some `x̂ ∈ (0,1)` has
`RD_n(x̂) = 1 - δ`, and every such `x̂` initializes a `δ`-ripple division
`x_0 = 0, x_1 = x̂, x_i = RD_i(x̂)`. -/
theorem lemma_2 (n : ℕ) (f : Fin n → ℝ → ℝ) (lam δ : ℝ) (hn : 2 ≤ n) (hf : IsInstance f)
    (hlam : 1 ≤ lam) (hL : QueriesLipschitz f lam) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (∃ xh ∈ Set.Ioo (0:ℝ) 1, rd f n xh = 1 - δ) ∧
    ∀ xh ∈ Set.Ioo (0:ℝ) 1, rd f n xh = 1 - δ → IsRipple f δ (fun k => rd f k xh) := by sorry

end MLRPCake.EnvyFree
