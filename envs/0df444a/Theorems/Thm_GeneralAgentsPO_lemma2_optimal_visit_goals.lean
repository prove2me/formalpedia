-- Prove2me | Theorems.Thm_GeneralAgentsPO_lemma2_optimal_visit_goals
-- name    : GeneralAgentsPO.lemma2_optimal_visit_goals
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:18:27.374074+00:00
-- url     : https://prove2.me/theorems/2c6c7fcb-a00f-4a40-85df-caa4d0ae7003
-- title:
--   Lemma 2 (as proved): optimal success probabilities of the goals $\varphi_{b,w}$ and $\rho_{b,r}$
-- statement:
--   Let $(\mathcal S,\mathcal A,P)$ be a finite communicating cMDP, let $s_0,s,s'\in\mathcal S$, $a,b\in\mathcal A$, $n\in\mathbb N$, and write $p=P(s'\mid s,a)$. Then there is a policy $\pi^*$ such that for every $w\in\{0,1\}^n$
--
--   $$\max_\pi\Pr(\varphi_{b,w}\mid\pi,s_0)=\Pr(\varphi_{b,w}\mid\pi^*,s_0)=p^{|w|_1}(1-p)^{n-|w|_1},$$
--
--   and for every $0\le r\le n$
--
--   $$\max_\pi\Pr(\rho_{b,r}\mid\pi,s_0)=\Pr(\rho_{b,r}\mid\pi^*,s_0)=\binom nr p^r(1-p)^{n-r}.$$
--
--   Here $\varphi_{b,w}$ asks that the first action be $b$ and that, at the $i$-th of the next $n$ visits to the pair $(s,a)$, the next state be $s'$ if $w_i=1$ and different from $s'$ if $w_i=0$; $\rho_{b,r}$ is the disjunction of the $\varphi_{b,w}$ with $|w|_1=r$. The policy $\pi^*$ takes $b$, then steers to $s$ and plays $a$ there.
--
--   **Formalization Note** The paper states that one policy $\pi^*$ works for every $b$. A single policy cannot take every action $b$ first with probability one, and when $|\mathcal A|\ge2$ and $p<1$ that reading is false. Its proof constructs a policy that takes action $b$ first, so the statement is formalized with $b$ fixed before $\pi^*$ is chosen.
-- source:
--   Cifuentes, General Agents Contain World Models, even under Partial Observability and Stochasticity, arXiv:2602.03146v1 (2026), Section 3, Lemma 2, eq. (2), p. 7 (goals of eq. (1), p. 6)

import Mathlib
import Definitions.Def_GeneralAgentsPO_Basic

open GeneralAgentsWorldModels

namespace GeneralAgentsPO

theorem lemma2_optimal_visit_goals {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (M : CMP S A) (hM : M.IsCommunicating) (s₀ s s' : S) (a b : A) (n : ℕ) :
    ∃ πstar : StochPolicy S A,
      (∀ w : Fin n → Bool,
        optValue M [trialSeq b s a s' (List.ofFn w)] s₀ =
            goalProb M πstar [trialSeq b s a s' (List.ofFn w)] s₀ ∧
          goalProb M πstar [trialSeq b s a s' (List.ofFn w)] s₀ =
            M.P s a s' ^ onesCount w * (1 - M.P s a s') ^ (n - onesCount w)) ∧
      ∀ r ≤ n,
        optValue M (binGoal b s a s' n (· = r)) s₀ =
            goalProb M πstar (binGoal b s a s' n (· = r)) s₀ ∧
          goalProb M πstar (binGoal b s a s' n (· = r)) s₀ = binPmf n (M.P s a s') r := by sorry

end GeneralAgentsPO
