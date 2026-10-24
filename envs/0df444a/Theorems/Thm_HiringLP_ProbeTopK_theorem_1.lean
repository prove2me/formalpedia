-- Prove2me | Theorems.Thm_HiringLP_ProbeTopK_theorem_1
-- name    : HiringLP.ProbeTopK.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:20.673983+00:00
-- url     : https://prove2.me/theorems/09fc1f8d-88bf-4c56-9af9-c3a9d4bbd877
-- title:
--   Theorem 1 — ALGptk earns at least (1 − e^{−k}k^k/k!) times LPptk(I)
-- statement:
--   Let $I$ be a valid ProbeTop-k instance with $k$ positions: $n$ applicants with independent values $V_i$ on $\{r_1,\dots,r_J\} \subseteq [0,\infty)$, $\Pr(V_i = r_j) = q_{ij}$, at most $T$ interviews, $1 \le k \le T \le n$. Let $(x, y)$ be an optimal basic feasible solution of $\mathrm{LP}_{ptk}(I)$, so that its objective is $\mathrm{LP}_{ptk}(I)$, and let the interview order be decreasing in $v_i = \sum_j r_j x_{ij} / \sum_j x_{ij}$ (ties broken arbitrarily). Let $R_{ALG_{ptk}}(I)$ be the expected reward of ALGptk: draw the interview set by the dependent rounding DR of $y$, interview in that order, and hire an interviewed applicant with value $r_j$ with probability $x_{ij}/(y_i q_{ij})$ while positions remain. Then
--
--   $$
--   R_{ALG_{ptk}}(I) \;\ge\; \Big(1 - \frac{e^{-k}k^k}{k!}\Big)\, \mathrm{LP}_{ptk}(I).
--   $$
--
--   Since $\mathrm{LP}_{ptk}(I)$ upper-bounds every (adaptive, non-committed) policy (Lemma 1), ALGptk, which is non-adaptive and committed, is a $(1 - e^{-k}k^k/k!)$-approximation; the factor is $1 - 1/e$ at $k = 1$ and tends to $1$ as $k$ grows.
--
--   **Formalization Note.** ALGptk solves the LP and applies DR, which needs at most two fractional coordinates; the LP solution is therefore taken optimal and an extreme point of the feasible polytope (a basic optimal solution, as a simplex solver returns). $\mathrm{LP}_{ptk}(I)$ is the objective at that optimal point. The expected reward is an explicit finite sum over the interview set, the value vector and the hiring coins, collecting the realised values of the hired applicants. The order is any permutation sorted by $v$, and $p_i, v_i$ and the hiring probabilities use footnote 2's zero conventions.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. 19, Theorem 1

import Mathlib
import Definitions.Def_HiringLP_ProbeTopK_Model

namespace HiringLP.ProbeTopK

theorem theorem_1 {n J : ℕ} (I : Instance n J) (hI : I.Valid)
    (x : Fin n → Fin J → ℝ) (y : Fin n → ℝ) (hopt : IsLPOpt I x y)
    (hext : (x, y) ∈ Set.extremePoints ℝ (feasibleSet I))
    (ord : Equiv.Perm (Fin n)) (hord : SortedBy ord (vbar I x)) :
    (1 - Real.exp (-(I.k : ℝ)) * (I.k : ℝ) ^ I.k / (I.k.factorial : ℝ)) * LPobj I x y ≤
      algReward I x y ord := by sorry

end HiringLP.ProbeTopK
