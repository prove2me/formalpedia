-- Prove2me | Theorems.Thm_GreedWorks_OnlineTime_lemma_7
-- name    : GreedWorks.OnlineTime.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:03:45.555295+00:00
-- url     : https://prove2.me/theorems/fbc1b2c1-6547-40b2-83ed-21c5cbd9266f
-- title:
--   Lemma 7 (feasibility), p. 15 — (α^f/a, β^f/b) is feasible for (D_r) when af ≥ 2(2+c), 1/c ≤ f(a−1), af ≥ b
-- statement:
--   Consider deterministic processing times $p_{ij}\ge1$ on eligible pairs, integer release dates $r_j$ with jobs indexed in release order, weights $w_j\ge0$, and an outcome $(m,s)$ of the online-time greedy algorithm with parameter $c>0$. Let $\alpha_j=\operatorname{cost}(j\to m(j))$, $\beta_{i,t}=\sum_{k:\,m(k)=i,\ r_k\le t,\ C_k\ge t}w_k$, and, for a speed $f\ge1$, $\alpha^f_j=\alpha_j/f$ and $\beta^f_{is}=\beta_{i,f\cdot s}$ as in (12). If $a,b>0$ and
--   $$af\ge 2(2+c),\qquad \frac1c\le f(a-1),\qquad af\ge b,$$
--   then $(\alpha^f/a,\;\beta^f/b)$ is a feasible solution of the dual $(\mathrm D_r)$ of the deterministic instance: $\beta^f_{is}/b\ge0$, $\sum_s\beta^f_{is}/b$ converges, and
--   $$\frac{\alpha^f_j}{a\,p_{ij}}\le\frac{\beta^f_{is}}{b}+w_j\Big(\frac{s+\frac12}{p_{ij}}+\frac12\Big)\qquad\text{for every eligible }(i,j)\text{ and every integer }s\ge r_j.$$
--
--   Feasibility of this dual point is the lower bound on the relaxation's optimum that the dual-fitting proofs of Theorems 3 and 4 use.
--
--   **Formalization Note** $f\ge1$ is the paper's standing assumption on speeds (p. 10, and "as long as $f\ge1$", p. 16). The lemma's second sentence, the objective bound $z^{D_r}(\alpha^f/a,\beta^f/b)\ge(\mathsf{ALG}/f)(1/a-1/b)$ at $c=\frac23$, $a=\frac{32}{23}$, $b=\frac{16}3$, $f=\frac{23}6$, is not stated: it fails on a one-machine instance with four jobs (see the mission description).
-- source:
--   Gupta, Moseley, Uetz & Xie, Greed Works – Online Algorithms For Unrelated Machine Stochastic Scheduling, arXiv:1703.01634v4, p. 15, Lemma 7 (first sentence); p. 14, (12)

import Mathlib
import Definitions.Def_GreedWorks_OnlineTime_TimeIndexedLP
import Definitions.Def_GreedWorks_OnlineTime_Greedy

namespace GreedWorks.OnlineTime

/-- Lemma 7, feasibility part (p. 15). Deterministic processing times `p_ij ≥ 1` on eligible
pairs, integer release dates in index order, weights `w ≥ 0`, and an outcome `(m, s)` of the
online-time greedy algorithm with parameter `c > 0`. With `α^f_j = α_j / f` and
`β^f_{is} = β_{i, f·s}` as in (12), `(α^f / a, β^f / b)` is feasible for the dual (D_r) of the
deterministic instance whenever `a, b > 0`, the speed is `f ≥ 1`, and
`af ≥ 2(2 + c)`, `1/c ≤ f(a − 1)`, `af ≥ b`. -/
theorem lemma_7 {M : Type*} [Fintype M] [Nonempty M] {n : ℕ}
    (elig : M → Fin n → Prop) (hElig : ∀ j, ∃ i, elig i j)
    (r : Fin n → ℕ) (hr : Monotone r)
    (p : M → Fin n → ℝ) (hp : ∀ i j, elig i j → 1 ≤ p i j)
    (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j)
    (c a b f : ℝ) (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) (hf : 1 ≤ f)
    (h₁ : 2 * (2 + c) ≤ a * f) (h₂ : 1 / c ≤ f * (a - 1)) (h₃ : b ≤ a * f)
    (m : Fin n → M) (s : Fin n → ℝ) (hG : IsGreedy c r p w elig m s) :
    IsFeasibleD elig r p w (fun j => alphaF c r p w m s f j / a)
      (fun i t => betaF r p w m s f i t / b) := by sorry

end GreedWorks.OnlineTime
