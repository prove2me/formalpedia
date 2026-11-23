-- Prove2me | Theorems.Thm_GeneralAgentsWorldModels_lemma6_optimal_success_binomial
-- name    : GeneralAgentsWorldModels.lemma6_optimal_success_binomial
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:37:58.818153+00:00
-- url     : https://prove2.me/theorems/225c6567-2214-4936-b44f-fd6e324182a7
-- title:
--   Lemma 6: the optimal success probability of $\psi(r,n)$ is binomial
-- statement:
--   Let the environment satisfy Assumption 1, let $s\ne s'$ be states, $a,b$ actions, and $0\le r\le n$. Let $\psi(r,n)$ be the disjunction of all sequential goals
--
--   $$\big\langle[A=b],\ \Diamond[S=s,A=a],\ \mathcal O_1,\ \Diamond[S=s,A=a],\ \mathcal O_2,\ \dots,\ \Diamond[S=s,A=a],\ \mathcal O_n\big\rangle$$
--
--   in which exactly $r$ of the $\mathcal O_i$ equal $\medcirc[S=s']$ and the other $n-r$ equal $\medcirc[S\ne s']$: the agent takes $b$, then $n$ times goes to $s$ and takes $a$, and the transition $(s,a)\to s'$ happens in exactly $r$ of these attempts. Then for every initial state $s_0$,
--
--   $$\max_\pi P(\tau\models\psi(r,n)\mid\pi,s_0)=\binom nr P_{ss'}(a)^r\big(1-P_{ss'}(a)\big)^{n-r}.$$
-- source:
--   Richens, Abel, Bellot and Everitt, General agents contain world models, arXiv:2506.01622v5 (ICML 2025), Appendix A.6, Lemma 6, eq. (25), pp. 16-17

import Mathlib
import Definitions.Def_GeneralAgentsWorldModels_Basic

open Finset

namespace GeneralAgentsWorldModels

theorem lemma6_optimal_success_binomial {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (M : CMP S A) (hM : SatisfiesAssumption1 M) (s s' : S) (a b : A) (hss : s ≠ s')
    (n r : ℕ) (hr : r ≤ n) (s₀ : S) :
    optProb M (binGoal b s a s' n (· = r)) s₀ =
      (n.choose r : ℝ) * M.P s a s' ^ r * (1 - M.P s a s') ^ (n - r) := by sorry

end GeneralAgentsWorldModels
