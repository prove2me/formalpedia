-- Prove2me | Theorems.Thm_HiringLP_SimLower_lemma_13
-- name    : HiringLP.SimLower.lemma_13
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:32.337103+00:00
-- url     : https://prove2.me/theorems/b928e15b-b32c-4a26-9900-82fdd9de5f0c
-- title:
--   Lemma 13 — if P_high ≤ k, ALG^s_sim earns ≥ (s − s/τ + E[min{Pois(sk),k}]/(τk)) LP_sim(I)
-- statement:
--   Let $s\in[0,1]$ and $\tau\in(0,1)$, and let $I=(k,n,p,v)$ be a valid $\tau$-bounded instance ($v_i\ge\tau$ for all $i$) with
--   $$\sum_{i\in V_{\mathrm{high}}}p_i\le k .$$
--   Let $(y,z)$ be any optimal solution of $\mathrm{LP}_{\mathrm{sim}}(I)$ and run $\mathrm{ALG}^s_{\mathrm{sim}}$ on $y$. Then
--   $$R_{\mathrm{ALG}^s_{\mathrm{sim}}}(I)\ \ge\ \Big(s-\frac{s}{\tau}+\frac{\mathbb E[\min\{\mathrm{Pois}(sk),k\}]}{\tau k}\Big)\,\mathrm{LP}_{\mathrm{sim}}(I).$$
--
--   This is the case of the main theorem in which the candidates of value above $1$ do not on their own exceed capacity in expectation.
--
--   **Formalization Note** The statement holds for every optimal LP solution (no tie hypothesis is needed). $R_{\mathrm{ALG}^s_{\mathrm{sim}}}(I)$ is the exact expected reward of the run defined in the algorithm file, not the bound obtained in the paper's proof.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. 29, Lemma 13

import Mathlib
import Definitions.Def_HiringLP_SimLower_Model
import Definitions.Def_HiringLP_SimLower_LP
import Definitions.Def_HiringLP_SimLower_Algorithm
import Definitions.Def_HiringLP_SimLower_PoissonRatio

namespace HiringLP.SimLower

/-- Lemma 13 (p. 29): for `s ∈ [0,1]`, `τ ∈ (0,1)` and a τ-bounded instance with `P_high ≤ k`, the
expected reward of `ALG^s_sim` run on an optimal LP solution is at least
`(s − s/τ + E[min{Pois(sk), k}]/(τk)) · LP_sim(I)`. -/
theorem lemma_13 {n : ℕ} (s τ : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (I : SimInstance n) (hI : I.Valid) (hτ : I.TauBounded τ) (hhigh : Phigh I ≤ I.k)
    (y : Fin n → ℝ) (z : ℝ) (hopt : IsLPOpt I y z) :
    ratioObj I.k τ s * LPsim I ≤ algReward I y s := by sorry

end HiringLP.SimLower
