-- Prove2me | Theorems.Thm_GeneralAgentsPO_lemma3_optimal_threshold_goals
-- name    : GeneralAgentsPO.lemma3_optimal_threshold_goals
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:19:12.548044+00:00
-- url     : https://prove2.me/theorems/902b4f0c-19d6-4cf1-b8df-b88116dcb616
-- title:
--   Lemma 3: optimal success probabilities of $\psi_{b,k}$ and $\chi_{b,k}$
-- statement:
--   Let $(\mathcal S,\mathcal A,P)$ be a finite communicating cMDP, let $s_0,s,s'\in\mathcal S$, $a,b\in\mathcal A$, $n\in\mathbb N$, $k\in\mathbb Z$ and $p=P(s'\mid s,a)$. With $\psi_{b,k}=\bigvee_{r\le k}\rho_{b,r}$ and $\chi_{b,k}=\bigvee_{r>k}\rho_{b,r}$ (eq. (3)),
--
--   $$\max_\pi\Pr(\psi_{b,k}\mid\pi,s_0)=\sum_{r\le k}\binom nr p^r(1-p)^{n-r},\qquad \max_\pi\Pr(\chi_{b,k}\mid\pi,s_0)=\sum_{r>k}\binom nr p^r(1-p)^{n-r},$$
--
--   the sums running over $0\le r\le n$. In other words, if $X\sim\mathrm{Bin}(n,p)$ then the best achievable probabilities of $\psi_{b,k}$ and $\chi_{b,k}$ are $\Pr(X\le k)$ and $\Pr(X>k)$.
--
--   **Formalization Note** $k$ is an integer because the proof of Theorem 2 uses $k=-1$. Each $\varphi_{b,w}$ with $|w|_1\le k$ (respectively $>k$) appears once as a disjunct, which is $\bigvee_{r\le k}\rho_{b,r}$ up to the order of the disjuncts.
-- source:
--   Cifuentes, General Agents Contain World Models, even under Partial Observability and Stochasticity, arXiv:2602.03146v1 (2026), Section 3, Lemma 3, eq. (3), pp. 7-8

import Mathlib
import Definitions.Def_GeneralAgentsPO_Basic

open GeneralAgentsWorldModels

namespace GeneralAgentsPO

theorem lemma3_optimal_threshold_goals {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (M : CMP S A) (hM : M.IsCommunicating) (s₀ s s' : S) (a b : A) (n : ℕ) (k : ℤ) :
    optValue M (binGoal b s a s' n (fun r => (r : ℤ) ≤ k)) s₀ =
        ∑ r ∈ (Finset.range (n + 1)).filter (fun r : ℕ => (r : ℤ) ≤ k), binPmf n (M.P s a s') r ∧
      optValue M (binGoal b s a s' n (fun r => k < (r : ℤ))) s₀ =
        ∑ r ∈ (Finset.range (n + 1)).filter (fun r : ℕ => k < (r : ℤ)), binPmf n (M.P s a s') r := by sorry

end GeneralAgentsPO
