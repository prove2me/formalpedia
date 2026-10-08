-- Prove2me | Theorems.Thm_ModPolicyIter_Conv_lemma_4
-- name    : ModPolicyIter.Conv.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:14:14.923885+00:00
-- url     : https://prove2.me/theorems/07ae9a44-d2a8-486a-9979-8b70741f3138
-- title:
--   Lemma 4, p. 1130 — u ∈ V_B implies (I + A^k B)u ∈ V_B
-- statement:
--   Throughout, $S$ is a set of states with a $\sigma$-algebra; each policy $P\in\mathcal P$ is a Markov transition kernel on $S$ with a measurable one-period reward $c_P$, $\sup_P\sup_s|c_P(s)|\le M$; $0\le\lambda<1$; $V$ is the space of bounded measurable functions with $\|v\|=\sup_s|v(s)|$; and the maximum in $Bv=\max_P\{c_P+(\lambda P-I)v\}$ is attained for every $v\in V$, a maximizer being written $P_v$.
--
--   Let $V_B=\{v\in V:Bv\ge 0\}$. If $u\in V_B$ and $P_u$ is a maximizer at $u$, then for every $k\ge 0$
--
--   $$u+A^k_{P_u}Bu\in V_B,\qquad A^k_{P_u}=\sum_{i=0}^k(\lambda P_u)^i .$$
--
--   The condition $Bv\ge 0$ is thus preserved by every step of modified policy iteration, which makes the iterates monotone (Theorem 1).
-- source:
--   Puterman and Shin, Modified policy iteration algorithms for discounted Markov decision problems, Management Science 24 (1978), DOI 10.1287/mnsc.24.11.1127, p. 1130, Lemma 4

import Mathlib
import Definitions.Def_ModPolicyIter_Conv_Setting

open MeasureTheory ProbabilityTheory

namespace ModPolicyIter.Conv

/-- Lemma 4 (Puterman–Shin 1978, p. 1130): if `u ∈ V_B` then `(I + A^k B)u ∈ V_B` for every
order `k`. -/
theorem lemma_4 {S : Type*} [MeasurableSpace S] {ι : Type*} (m : Model S ι)
    (hmax : MaxAttained m) (k : ℕ) :
    ∀ u ∈ VB m, ∀ i, Attains m u i → (u + Apow m i k (B m u)) ∈ VB m := by sorry

end ModPolicyIter.Conv
