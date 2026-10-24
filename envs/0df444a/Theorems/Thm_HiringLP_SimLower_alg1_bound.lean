-- Prove2me | Theorems.Thm_HiringLP_SimLower_alg1_bound
-- name    : HiringLP.SimLower.alg1_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:37.83614+00:00
-- url     : https://prove2.me/theorems/21432eac-4daa-464c-97d6-8d52ddef698c
-- title:
--   §6.4, p. 30 — on τ-bounded instances ALG¹_sim earns ≥ (1 − e^{−k}k^k/(k!τ)) LP_sim(I)
-- statement:
--   Let $\tau\in(0,1)$ and let $I=(k,n,p,v)$ be a valid $\tau$-bounded instance. Let $(y,z)$ be any optimal solution of $\mathrm{LP}_{\mathrm{sim}}(I)$. The algorithm $\mathrm{ALG}^1_{\mathrm{sim}}$, which follows the LP solution without truncation ($s=1$), satisfies
--   $$R_{\mathrm{ALG}^1_{\mathrm{sim}}}(I)\ \ge\ \Big(1-\frac{e^{-k}k^k}{k!\,\tau}\Big)\,\mathrm{LP}_{\mathrm{sim}}(I).$$
--
--   Combined with Stirling's formula this gives the $1-O(1/\sqrt k)$ guarantee of Corollary 4.
--
--   **Formalization Note** The paper derives this bound "by Lemma 13" and Proposition EC.2 and states it as a guarantee of $\mathrm{ALG}^1_{\mathrm{sim}}$ on $\tau$-bounded instances; it is stated here for every $\tau$-bounded instance, including the case $\sum_{i\in V_{\mathrm{high}}}p_i>k$ that Lemma 13 does not cover. The algorithm uses $y$ only through its total mass $\sum_i y_ip_i$; the statement holds for every optimal $(y,z)$.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. 30, §6.4, paragraph after Theorem 3

import Mathlib
import Definitions.Def_HiringLP_SimLower_Model
import Definitions.Def_HiringLP_SimLower_LP
import Definitions.Def_HiringLP_SimLower_Algorithm
import Definitions.Def_HiringLP_SimLower_PoissonRatio

namespace HiringLP.SimLower

/-- §6.4, p. 30 (consequence of Lemma 13 and Proposition EC.2): for `τ ∈ (0,1)` and every τ-bounded
instance, `ALG¹_sim` run on an optimal LP solution earns at least `(1 − e^{−k} kᵏ / (k! τ)) · LP_sim(I)`. -/
theorem alg1_bound {n : ℕ} (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (I : SimInstance n) (hI : I.Valid) (hτ : I.TauBounded τ)
    (y : Fin n → ℝ) (z : ℝ) (hopt : IsLPOpt I y z) :
    (1 - Real.exp (-(I.k : ℝ)) * (I.k : ℝ) ^ I.k / ((I.k.factorial : ℝ) * τ)) * LPsim I ≤
      algReward I y 1 := by sorry

end HiringLP.SimLower
