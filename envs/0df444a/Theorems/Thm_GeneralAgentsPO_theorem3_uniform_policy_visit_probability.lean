-- Prove2me | Theorems.Thm_GeneralAgentsPO_theorem3_uniform_policy_visit_probability
-- name    : GeneralAgentsPO.theorem3_uniform_policy_visit_probability
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:20:31.988388+00:00
-- url     : https://prove2.me/theorems/6c30e866-a298-4a06-b9b0-523e0b6e0792
-- title:
--   Theorem 3 (proof, eq. (5)): the uniformly random observation-based policy achieves $\varphi_w$ with probability $p^{|w|_1}(1-p)^{n-|w|_1}$
-- statement:
--   Let $(\mathcal S,\mathcal A,P,O,\Omega)$ be a finite partially observable cMDP whose cMDP is communicating, and let $\pi$ be the observation-based policy that always picks an action uniformly at random: $\Pr(\pi(o_0a_0\dots o_t)=c)=1/|\mathcal A|$ for every finite observation history and every $c\in\mathcal A$. Let $s,s'\in\mathcal S$, $a\in\mathcal A$, $p=P(s'\mid s,a)$, and for $w\in\{0,1\}^n$ let $\varphi_w=\langle\varphi_2,\varphi_3^{w_1},\dots,\varphi_2,\varphi_3^{w_n}\rangle$. Then for every start state $s_0$
--
--   $$\Pr(\varphi_w\mid\pi,s_0)=p^{|w|_1}(1-p)^{n-|w|_1}.$$
--
--   This is the step of the proof of Theorem 3 (built on eq. (5)) showing that, for goals phrased in states, the observation kernel plays no role for a policy that ignores its observations. In a finite communicating cMDP the uniformly random policy visits $(s,a)$ infinitely often.
-- source:
--   Cifuentes, General Agents Contain World Models, even under Partial Observability and Stochasticity, arXiv:2602.03146v1 (2026), Section 4.2, proof of Theorem 3, eq. (5), pp. 13-14

import Mathlib
import Definitions.Def_GeneralAgentsPO_Basic

open GeneralAgentsWorldModels

namespace GeneralAgentsPO

theorem theorem3_uniform_policy_visit_probability {S A O : Type*} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Fintype O] (M : POCMP S A O) (hM : M.toCMP.IsCommunicating)
    (π : StochPolicy O A) (hπ : ∀ h o c, π.act h o c = 1 / Fintype.card A)
    (s s' : S) (a : A) (n : ℕ) (w : Fin n → Bool) (s₀ : S) :
    obsGoalProb M π [visitSeq s a s' (List.ofFn w)] s₀ =
      M.P s a s' ^ onesCount w * (1 - M.P s a s') ^ (n - onesCount w) := by sorry

end GeneralAgentsPO
